-- Prove2me | Theorems.Thm_AgnosticTNS_Supplement_theorem_6_16
-- name    : AgnosticTNS.Supplement.theorem_6_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:49:36.475622+00:00
-- url     : https://prove2.me/theorems/fbf32d13-7e57-496b-ae2d-5d3f6af5aa40
-- title:
--   Theorem 6.16 — tomography through an MPS representation, $O(n^3\epsilon^{-4}(\chi^cd^{\kappa_c+1}+\log(n/\delta)))$ copies
-- statement:
--   Let $G=([n],E)$, $n\ge1$, $d\ge2$, $\chi\ge1$, and let $\pi$ be a linear ordering of the vertices; set $c=\mathrm{cw}(\pi)$ and $\kappa_c=\max\{1,\lceil\log_d(\chi^c)\rceil\}$ (6.39). Then an unknown $|\psi\rangle\in S_d(G,\chi)$ can be learned to trace-norm error at most $\epsilon$ with success probability at least $1-\delta$ using
--   $$
--   O\Big(\frac{n^3}{\epsilon^4}\big(\chi^c d^{\kappa_c+1}+\log(n/\delta)\big)\Big)\quad(6.40)
--   $$
--   copies; if $\pi$ has optimal cutwidth, $O\big(\frac{n^3}{\epsilon^4}(d^2\chi^{2\,\mathrm{cw}(G)}+\log(n/\delta))\big)$ copies suffice (6.41). The classical processing time is polynomial in $n$, $d^{\kappa_c+1}$, $\chi^c$, $1/\epsilon$ and $\log(1/\delta)$.
--
--   This gives realisable tomography for any graph with copy complexity governed by its cutwidth.
--
--   **Formalization Note** One learner family on instances $(G,\pi,d,\chi,\lceil1/\epsilon\rceil,\lceil\log_2(1/\delta)\rceil)$ acting on the original qudits, one absolute constant, and a polynomial-time printer from the instance padded with $n+d^{\kappa_c+1}+\chi^c+\lceil1/\epsilon\rceil+\lceil\log_2(1/\delta)\rceil$.
--
--   Differences from the source:
--   - generalization: classical post-processing time polynomial in n, d^{κ_c+1}, χ^c, ⌈1/ε⌉, ⌈log₂(1/δ)⌉, assuming the tomography primitive and eigendecompositions run in polynomial time → unconditional: a polynomial-time printer of the learner's circuit from the instance padded in unary with n, d^{κ_c+1}, χ^c, ⌈1/ε⌉, ⌈log₂(1/δ)⌉; reason: the paper names the primitive (Lemma 3.9, pp.38, 59), which runs in polynomial time; the unconditional statement implies the conditional one
--   - encoding: O(·) bounds → one absolute constant C > 0 chosen before every instance parameter; reason: the base mission's reading of O(·); no constant depends on n, L, d, χ, w, k, ε or δ
--   - encoding: an algorithm receiving copies, ε and δ → one learner family (a Clifford+T circuit on qubit encodings of the copies plus ancillas, measured at the end) indexed by the instance with ⌈1/ε⌉ and ⌈log₂(1/δ)⌉; reason: the base mission's learner model; real ε ∈ (0, 1], δ ∈ (0, 1) remain the guarantee's parameters
--   - encoding: output a pure state with trace-norm error at most ε → the output decodes with the fixed decoder decodeTTN to a TTN whose normalised state is within trace norm ε of |ψ⟩⟨ψ|; reason: Gaussian-rational TTN entries cannot be exactly normalised; same guarantee
--   - encoding: G = ([n], E) → 1 ≤ n; reason: the vertex set [n] is nonempty (an empty graph has no state to learn); log(n/δ) is then positive
--   - reading: If the ordering π is not given, an optimal cutwidth ordering can first be computed in time 2^{O(cw(G)²)} n → not stated; reason: the sentence reports the algorithm of [TSB05a, TSB05b], cited and not proved in the paper; the theorem's running time excludes it ('apart from this graph preprocessing step')
--   - encoding: κ_c = max{1, ⌈log_d(χ^c)⌉}; (6.41) when π is chosen to have optimal cutwidth → max 1 (Nat.clog d (χ^c)); a conjunct under cw(π) = cw(G); reason: equal for d ≥ 2, χ ≥ 1
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.16, Eqs. (6.39)–(6.41), p.59

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_prob
import Definitions.Def_AgnosticTNS_CopyLearner_code
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_AgnosticTNS_Supplement_encOrdIndex
import Definitions.Def_AgnosticTNS_Supplement_cwGraph
import Definitions.Def_AgnosticTNS_Supplement_RealSuccess
import Definitions.Def_AgnosticTNS_TNSchi
open Matrix
open QAlgorithms.Complexity

namespace AgnosticTNS.Supplement

/-- **Theorem 6.16 (Tomography using an MPS representation)**, p.59 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
Let `G = ([n], E)` and `π : [n] → [n]` a linear ordering; set `c = cw(π)`, `κ_c = max{1, ⌈log_d(χ^c)⌉}`
(6.39). Then an unknown `|ψ⟩ ∈ S_d(G, χ)` can be learned to trace-norm error at most `ϵ` with success
probability at least `1 − δ` using `O(n³/ϵ⁴ · (χ^c d^{κ_c+1} + log(n/δ)))` copies (6.40). In particular, if
`π` has optimal cutwidth, `O(n³/ϵ⁴ · (d²χ^{2cw(G)} + log(n/δ)))` copies suffice (6.41). The classical
post-processing time of the sequential learner is polynomial in `n, d^{κ_c+1}, χ^c, 1/ϵ, log(1/δ)`.

**Formalization Note** `n ≥ 1`, `d ≥ 2`, `χ ≥ 1`. One learner family on `(n, G, π, d, χ, ⌈1/ϵ⌉,
⌈log₂(1/δ)⌉)` (acting on the original `n` qudits), one absolute constant, one polynomial-time printer of the
Clifford+T circuit from the instance padded with `n + d^{κ_c+1} + χ^c + ⌈1/ϵ⌉ + ⌈log₂(1/δ)⌉`; the
polynomial-time primitive assumption is discharged (Lemma 3.9). `⌈log_d(χ^c)⌉ = Nat.clog d (χ^c)`.
Success is `RealSuccess` (4.1). The sentence on computing an optimal ordering in time `2^{O(cw(G)²)} n`
cites [TSB05a, TSB05b] and is not stated. -/
theorem theorem_6_16 :
    ∃ (Lr : CopyLearner OrdIndex (fun i => i.n) (fun i => i.d)) (C : ℝ) (g : Str → Str),
      0 < C ∧ PolyTimeComputable g ∧
      ∀ (n d χ : ℕ) (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (ε δ : ℝ),
        1 ≤ n → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        let c := cwOrd G π
        let κc := max 1 (Nat.clog d (χ ^ c))
        let i : OrdIndex := ⟨n, G, π, d, χ, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩
        g (encOrdIndex i ++ unary (n + d ^ (κc + 1) + χ ^ c + ⌈1 / ε⌉₊ + ⌈Real.logb 2 (1 / δ)⌉₊)) = Lr.code i ∧
          (Lr.copies i : ℝ) ≤ C * (n : ℝ) ^ 3 / ε ^ 4 *
            ((χ : ℝ) ^ c * (d : ℝ) ^ (κc + 1) + Real.log (n / δ)) ∧
          (c = cwGraph G → (Lr.copies i : ℝ) ≤ C * (n : ℝ) ^ 3 / ε ^ 4 *
            ((d : ℝ) ^ 2 * (χ : ℝ) ^ (2 * cwGraph G) + Real.log (n / δ))) ∧
          ∀ ψ ∈ TNSchi d G χ, 1 - δ ≤ Lr.prob i (vecMulVec ψ (star ψ)) (RealSuccess ψ ε) := by sorry

end AgnosticTNS.Supplement
