-- Prove2me | Theorems.Thm_AgnosticTNS_Supplement_theorem_1_3
-- name    : AgnosticTNS.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:44:08.122076+00:00
-- url     : https://prove2.me/theorems/1c1f5fa3-ac12-4edf-b03d-75798daa5593
-- title:
--   Theorem 1.3 — realisable tomography from learning sequences, $\mathrm{lc}_{d,\chi}(G)$, and on trees
-- statement:
--   Let $G=([n],E)$ be a graph, $d\ge2$, $\chi\ge1$, $\epsilon\in(0,1]$, $\delta\in(0,1)$. Learning means outputting, with probability at least $1-\delta$, a pure state within trace norm $\epsilon$ of the unknown $|\psi\rangle\in S_d(G,\chi)$.
--   1. Given a learning sequence $\mathcal L=(S_i,I_i,F_i)_{i=1}^L$ with $r_i=\chi^{|\mathrm{cut}_G(S_i)|}$, $q_i=\lceil\log_d r_i\rceil$, $a_i=|F_i|+\sum_{j\in I_i}q_j$, the unknown state can be learned with
--   $$
--   O\Big(\frac{L^3}{\epsilon^4}\Big(\max_{i\in[L]} r_i d^{a_i} + \log(L/\delta)\Big)\Big)\quad(1.5)
--   $$
--   copies.
--   2. In particular, run on a normalised learning sequence attaining $\mathrm{lc}_{d,\chi}(G)$, the learner uses $O\big(\frac{n^3}{\epsilon^4}(d^{\mathrm{lc}_{d,\chi}(G)}+\log(n/\delta))\big)$ copies (1.6).
--   3. For a connected graph with at least two vertices,
--   $$
--   \mathrm{lc}_{d,\chi}(G) \le \min\{n,\ 3\max\{1,\lceil \mathrm{cc}(G)\log_d\chi\rceil\}\}.\quad(1.7)
--   $$
--   4. For a known tree $T$ of maximum degree $\Delta$, a specialised learner uses $O\big(\frac{n^3}{\epsilon^4}((d\chi)^{\max\{2,\Delta\}}+\log(n/\delta))\big)$ copies (1.8).
--
--   These bounds show that the rank constraints of the reference class allow tomography with fewer copies than the agnostic learner, governed by the learning complexity of the graph.
--
--   **Formalization Note** One learner family with one absolute constant serves (1.5) and (1.6); (1.6) bounds its copies on every normalised sequence $\mathcal L$ with $\mathrm{lc}_{d,\chi}(\mathcal L)=\mathrm{lc}_{d,\chi}(G)$. In (1.7), $\lceil\mathrm{cc}(G)\log_d\chi\rceil$ is written $\lceil\log_d\chi^{\mathrm{cc}(G)}\rceil$ (`Nat.clog`). (1.8) is a separate learner family on tree instances, $T$ on $n\ge1$ vertices.
--
--   Differences from the source:
--   - encoding: O(·) bounds → one absolute constant C > 0 chosen before every instance parameter; reason: the base mission's reading of O(·); no constant depends on n, L, d, χ, w, k, ε or δ
--   - encoding: an algorithm receiving copies, ε and δ → one learner family (a Clifford+T circuit on qubit encodings of the copies plus ancillas, measured at the end) indexed by the instance with ⌈1/ε⌉ and ⌈log₂(1/δ)⌉; reason: the base mission's learner model; real ε ∈ (0, 1], δ ∈ (0, 1) remain the guarantee's parameters
--   - encoding: output a pure state with trace-norm error at most ε → the output decodes with the fixed decoder decodeTTN to a TTN whose normalised state is within trace norm ε of |ψ⟩⟨ψ|; reason: Gaussian-rational TTN entries cannot be exactly normalised; same guarantee
--   - reading: (1.6) copies suffice, given a normalised learning sequence attaining lc_{d,χ}(G) → for every normalised learning sequence L with lc_{d,χ}(L) = lc_{d,χ}(G), the (1.5) learner run on L uses at most C n³/ε⁴ (d^{lc_{d,χ}(G)} + log(n/δ)) copies; reason: the learner of (1.5) is the one run on that sequence; normalisation gives L ≤ 2n − 1
--   - encoding: ⌈cc(G) log_d χ⌉ → Nat.clog d (χ^{cc(G)}); reason: equal for d ≥ 2 and χ ≥ 1
--   - reading: (1.8) for a known tree T of maximum degree Δ, the specialised learner → a learner family on tree instances (n, T, d, χ, ⌈1/ε⌉, ⌈log₂(1/δ)⌉) for every tree on n ≥ 1 vertices, Δ = T.maxDegree; reason: the specialised learner is Algorithm 6 (Theorem 4.10, which assumes n ≥ 1)
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 1.3, Eqs. (1.5)–(1.8), p.4 (with Remark 2.6, p.14, Corollary 5.6, p.41, Theorem 4.10, p.38)

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_prob
import Definitions.Def_AgnosticTNS_TreeIndex
import Definitions.Def_AgnosticTNS_Supplement_RSeqIndex
import Definitions.Def_AgnosticTNS_Supplement_RealSuccess
import Definitions.Def_AgnosticTNS_Supplement_aR
import Definitions.Def_AgnosticTNS_Supplement_lcGraph
import Definitions.Def_AgnosticTNS_Supplement_IsNormalised
import Definitions.Def_AgnosticTNS_Supplement_cc
import Definitions.Def_AgnosticTNS_rr
import Definitions.Def_AgnosticTNS_TNSchi
open Matrix
open QAlgorithms.Complexity
open Classical

namespace AgnosticTNS.Supplement

/-- **Theorem 1.3 (Realisable tomography, informal)**, p.4 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
Given a learning sequence `L = (S_i, I_i, F_i)_{i=1}^L` with parameters `r_i, q_i, a_i`, an unknown state in
`S_d(G, χ)` can be learned using `O(L³/ϵ⁴ · (max_i r_i d^{a_i} + log(L/δ)))` copies (1.5). In particular
`O(n³/ϵ⁴ · (d^{lc_{d,χ}(G)} + log(n/δ)))` copies suffice (1.6), given a normalised learning sequence
attaining `lc_{d,χ}(G)`. For a connected graph with at least two vertices,
`lc_{d,χ}(G) ≤ min{n, 3 max{1, ⌈cc(G) log_d χ⌉}}` (1.7). For a known tree `T` of maximum degree `Δ`, the
specialised learner uses `O(n³/ϵ⁴ · ((dχ)^{max{2,Δ}} + log(n/δ)))` copies (1.8).

**Formalization Note** "Learned" is the realisable guarantee (4.1) (`RealSuccess`, trace-norm error
`ϵ` with probability `≥ 1 − δ`). (1.5)–(1.6): one learner family on the instances
`(n, G, L, d, χ, none, ⌈1/ϵ⌉, ⌈log₂(1/δ)⌉)` with one absolute constant; (1.6) bounds its copies on every
normalised sequence with `lc_{d,χ}(L) = lc_{d,χ}(G)`. (1.7): `⌈cc(G) log_d χ⌉ = ⌈log_d χ^{cc(G)}⌉ =
Nat.clog d (χ^{cc(G)})`. (1.8): a learner family on `(n, T, d, χ, ⌈1/ϵ⌉, ⌈log₂(1/δ)⌉)`, `Δ = T.maxDegree`.
The theorem makes no running-time claim. -/
theorem theorem_1_3 :
    (∃ (Lr : CopyLearner RSeqIndex (fun i => i.n) (fun i => i.d)) (C : ℝ), 0 < C ∧
      ∀ (n d χ : ℕ) (G : SimpleGraph (Fin n)) (Ls : LearningSequence n) (ε δ : ℝ),
        2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        let i : RSeqIndex := ⟨n, G, Ls, d, χ, none, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩
        (Lr.copies i : ℝ) ≤ C * (Ls.L : ℝ) ^ 3 / ε ^ 4 *
            (((Finset.univ.sup fun j => rr G χ Ls j * d ^ aR d Ls (rr G χ Ls) j : ℕ) : ℝ) +
              Real.log (Ls.L / δ)) ∧
          (IsNormalised Ls → lcSeq d Ls (rr G χ Ls) = lcGraph d G χ →
            (Lr.copies i : ℝ) ≤ C * (n : ℝ) ^ 3 / ε ^ 4 *
              ((d : ℝ) ^ lcGraph d G χ + Real.log (n / δ))) ∧
          ∀ ψ ∈ TNSchi d G χ, 1 - δ ≤ Lr.prob i (vecMulVec ψ (star ψ)) (RealSuccess ψ ε)) ∧
    (∀ (n d χ : ℕ) (G : SimpleGraph (Fin n)), G.Connected → 2 ≤ n → 2 ≤ d → 1 ≤ χ →
      lcGraph d G χ ≤ min n (3 * max 1 (Nat.clog d (χ ^ cc G)))) ∧
    (∃ (Lt : CopyLearner TreeIndex (fun i => i.n) (fun i => i.d)) (C : ℝ), 0 < C ∧
      ∀ (n d χ : ℕ) (T : SimpleGraph (Fin n)) (ε δ : ℝ),
        1 ≤ n → T.IsTree → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        let i : TreeIndex := ⟨n, T, d, χ, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩
        (Lt.copies i : ℝ) ≤ C * (n : ℝ) ^ 3 / ε ^ 4 *
            (((d : ℝ) * χ) ^ max 2 T.maxDegree + Real.log (n / δ)) ∧
          ∀ ψ ∈ TNSchi d T χ, 1 - δ ≤ Lt.prob i (vecMulVec ψ (star ψ)) (RealSuccess ψ ε)) := by sorry

end AgnosticTNS.Supplement
