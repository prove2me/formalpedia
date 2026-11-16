-- Prove2me | Theorems.Thm_AgnosticTNS_Supplement_theorem_4_10
-- name    : AgnosticTNS.Supplement.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:46:31.080312+00:00
-- url     : https://prove2.me/theorems/81405fa3-7725-4a31-be0b-e31ec30fed0c
-- title:
--   Theorem 4.10 — TTN state tomography with $O(n^3\epsilon^{-4}(\chi d^{1+b\kappa}+\log(n/\delta)))$ copies
-- statement:
--   Let $T$ be a tree on $n\ge1$ vertices with maximum degree $\Delta$, $d\ge2$, $\chi\ge1$, $\kappa=\max\{1,\lceil\log_d\chi\rceil\}$, and $b$ the maximum number of children when $T$ is rooted at a leaf as in Algorithm 6. Algorithm 6 learns every unknown $|\psi\rangle\in S_d(T,\chi)$ to trace-norm error at most $\epsilon$ with success probability at least $1-\delta$ using
--   $$
--   O\Big(\frac{n^3}{\epsilon^4}\big(\chi d^{1+b\kappa}+\log(n/\delta)\big)\Big)\quad(4.83)
--   $$
--   copies. Moreover $\chi d^{1+b\kappa}\le(d\chi)^{\max\{2,\Delta\}}$ (4.84) and, for $n\ge3$, $\chi d^{1+b\kappa}\le(d\chi)^{\Delta}$ (4.85); thus for $n\ge3$ the copy complexity is $O\big(\frac{n^3}{\epsilon^4}((d\chi)^\Delta+\log(n/\delta))\big)$ (4.86). The runtime is polynomial in $n$, $d^{1+b\kappa}$, $\chi$, $1/\epsilon$ and $\log(1/\delta)$.
--
--   For bounded degree this gives realisable TTN tomography with copies and time polynomial in $n$, $d$, $\chi$.
--
--   **Formalization Note** $b$ is the published `leafBranching` (for a tree every leaf root gives the same maximum number of children; $b=0$ for $n=1$). One learner family, one absolute constant, and a polynomial-time printer from the instance padded with $n+d^{1+b\kappa}+\chi+\lceil1/\epsilon\rceil+\lceil\log_2(1/\delta)\rceil$.
--
--   Differences from the source:
--   - generalization: classical post-processing time polynomial in n, d^{1+bκ}, χ, ⌈1/ε⌉, ⌈log₂(1/δ)⌉, assuming the tomography primitive and eigendecompositions run in polynomial time → unconditional: a polynomial-time printer of the learner's circuit from the instance padded in unary with n, d^{1+bκ}, χ, ⌈1/ε⌉, ⌈log₂(1/δ)⌉; reason: the paper names the primitive (Lemma 3.9, pp.38, 59), which runs in polynomial time; the unconditional statement implies the conditional one
--   - encoding: O(·) bounds → one absolute constant C > 0 chosen before every instance parameter; reason: the base mission's reading of O(·); no constant depends on n, L, d, χ, w, k, ε or δ
--   - encoding: an algorithm receiving copies, ε and δ → one learner family (a Clifford+T circuit on qubit encodings of the copies plus ancillas, measured at the end) indexed by the instance with ⌈1/ε⌉ and ⌈log₂(1/δ)⌉; reason: the base mission's learner model; real ε ∈ (0, 1], δ ∈ (0, 1) remain the guarantee's parameters
--   - encoding: output a pure state with trace-norm error at most ε → the output decodes with the fixed decoder decodeTTN to a TTN whose normalised state is within trace norm ε of |ψ⟩⟨ψ|; reason: Gaussian-rational TTN entries cannot be exactly normalised; same guarantee
--   - encoding: b = max_u |ch(u)| after the rooting chosen in the algorithm → leafBranching T (minimum over leaf roots of the maximum number of children; 0 for n = 1); reason: Algorithm 6 roots at a degree-one vertex (p.72); every leaf root of a tree gives the same value
--   - encoding: κ = max{1, ⌈log_d χ⌉}; Δ = Δ(T) → max 1 (Nat.clog d χ); T.maxDegree; reason: equal for d ≥ 2, χ ≥ 1
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 4.10, Eqs. (4.83)–(4.86), p.38; Algorithm 6, p.72

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_prob
import Definitions.Def_AgnosticTNS_CopyLearner_code
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_AgnosticTNS_encTreeIndex
import Definitions.Def_AgnosticTNS_leafBranching
import Definitions.Def_AgnosticTNS_Supplement_RealSuccess
import Definitions.Def_AgnosticTNS_TNSchi
open Matrix
open QAlgorithms.Complexity
open Classical

namespace AgnosticTNS.Supplement

/-- **Theorem 4.10 (TTN state tomography)**, p.38 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
Let `T` be a tree on `n ≥ 1` vertices with maximum degree `Δ = Δ(T)` and `|ψ⟩ ∈ S_d(T, χ)` unknown, `d ≥ 2`.
Given `T, d, χ`, Algorithm 6 learns `|ψ⟩` to trace-norm error at most `ϵ` with success probability at
least `1 − δ` using `O(n³/ϵ⁴ · (χ d^{1+bκ} + log(n/δ)))` copies (4.83), `κ = max{1, ⌈log_d χ⌉}`, `b` the
maximum number of children in the rooting of the algorithm. In particular `χ d^{1+bκ} ≤ (dχ)^{max{2,Δ}}`
(4.84) and, for `n ≥ 3`, `χ d^{1+bκ} ≤ (dχ)^Δ` (4.85); thus for `n ≥ 3` the copy complexity is
`O(n³/ϵ⁴ · ((dχ)^Δ + log(n/δ)))` (4.86). The runtime is polynomial in `n, d^{1+bκ}, χ, 1/ϵ, log(1/δ)`.

**Formalization Note** Algorithm 6 roots `T` at a degree-one vertex (p.72); `b = leafBranching T`
(for a tree every leaf root gives the same maximum number of children; `0` for `n = 1`).
`Δ = T.maxDegree`, `⌈log_d χ⌉ = Nat.clog d χ`. One learner family, one absolute constant, one
polynomial-time printer from the instance padded with `n + d^{1+bκ} + χ + ⌈1/ϵ⌉ + ⌈log₂(1/δ)⌉`; the
polynomial-time primitive assumption is discharged (Lemma 3.9). Success is `RealSuccess` (4.1). -/
theorem theorem_4_10 :
    ∃ (Lr : CopyLearner TreeIndex (fun i => i.n) (fun i => i.d)) (C : ℝ) (g : Str → Str),
      0 < C ∧ PolyTimeComputable g ∧
      ∀ (n d χ : ℕ) (T : SimpleGraph (Fin n)) (ε δ : ℝ),
        1 ≤ n → T.IsTree → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        let κ := max 1 (Nat.clog d χ)
        let b := leafBranching T
        let i : TreeIndex := ⟨n, T, d, χ, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩
        g (encTreeIndex i ++ unary (n + d ^ (1 + b * κ) + χ + ⌈1 / ε⌉₊ + ⌈Real.logb 2 (1 / δ)⌉₊)) = Lr.code i ∧
          (Lr.copies i : ℝ) ≤ C * (n : ℝ) ^ 3 / ε ^ 4 *
            ((χ : ℝ) * (d : ℝ) ^ (1 + b * κ) + Real.log (n / δ)) ∧
          χ * d ^ (1 + b * κ) ≤ (d * χ) ^ max 2 T.maxDegree ∧
          (3 ≤ n → χ * d ^ (1 + b * κ) ≤ (d * χ) ^ T.maxDegree) ∧
          (3 ≤ n → (Lr.copies i : ℝ) ≤ C * (n : ℝ) ^ 3 / ε ^ 4 *
            (((d : ℝ) * χ) ^ T.maxDegree + Real.log (n / δ))) ∧
          ∀ ψ ∈ TNSchi d T χ, 1 - δ ≤ Lr.prob i (vecMulVec ψ (star ψ)) (RealSuccess ψ ε) := by sorry

end AgnosticTNS.Supplement
