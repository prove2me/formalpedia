-- Prove2me | Theorems.Thm_AgnosticTNS_Supplement_theorem_6_18
-- name    : AgnosticTNS.Supplement.theorem_6_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:51:08.934353+00:00
-- url     : https://prove2.me/theorems/43314749-512d-4ae4-96d9-5761321924aa
-- title:
--   Theorem 6.18 — tomography through a tree-cut decomposition
-- statement:
--   Let $G=([n],E)$, $d\ge2$, $\chi\ge1$, and let $(\mathcal T,\mathcal X)$ be a tree-cut decomposition of $G$ of width at most $k\ge1$. Let $(\hat T,\hat{\mathcal X})$ be obtained from it by removing empty bags as in Lemma 6.13, $m=|V(\hat T)|$ (6.46), $b_{\hat T}$ the maximum number of children of $\hat T$ rooted as in Algorithm 6 (6.47), and $\kappa=\max\{1,\lceil\log_d\chi\rceil\}$ (6.48). Then an unknown $|\psi\rangle\in S_d(G,\chi)$ can be learned to trace-norm error at most $\epsilon$ with success probability at least $1-\delta$ using
--   $$
--   O\Big(\frac{m^3}{\epsilon^4}\big(\chi^k d^{k(1+b_{\hat T}\kappa)}+\log(m/\delta)\big)\Big)\quad(6.49)
--   $$
--   copies. Consequently $O\big(\frac{n^3}{\epsilon^4}((d\chi)^{k\max\{2,\Delta(\hat T)\}}+\log(n/\delta))\big)$ copies suffice (6.50); if $m\ge3$, $O\big(\frac{n^3}{\epsilon^4}((d\chi)^{k\Delta(\hat T)}+\log(n/\delta))\big)$ (6.51); and when $k\le2\,\mathrm{tcw}(G)$, $O\big(\frac{n^3}{\epsilon^4}((d\chi)^{2\,\mathrm{tcw}(G)\max\{2,\Delta(\hat T)\}}+\log(n/\delta))\big)$ (6.52). The classical processing time, once the decomposition is chosen, is polynomial in $m$, $d^{k(1+b_{\hat T}\kappa)}$, $\chi^k$, $1/\epsilon$ and $\log(1/\delta)$.
--
--   This gives realisable tomography for any graph with copy complexity governed by its tree-cutwidth and the degree of the decomposition tree.
--
--   **Formalization Note** The learner's input is $(G,\hat T,\hat{\mathcal X},k,d,\chi,\lceil1/\epsilon\rceil,\lceil\log_2(1/\delta)\rceil)$, with the hypothesis that some tree-cut decomposition of width at most $k$ yields $(\hat T,\hat{\mathcal X})$; $b_{\hat T}$ is the published `leafBranching`; the learner acts on the original $n$ qudits; one absolute constant and a polynomial-time printer from the instance padded with $n+m+d^{k(1+b_{\hat T}\kappa)}+\chi^k+\lceil1/\epsilon\rceil+\lceil\log_2(1/\delta)\rceil$.
--
--   Differences from the source:
--   - generalization: classical post-processing time polynomial in n, m, d^{k(1+b κ)}, χ^k, ⌈1/ε⌉, ⌈log₂(1/δ)⌉, assuming the tomography primitive and eigendecompositions run in polynomial time → unconditional: a polynomial-time printer of the learner's circuit from the instance padded in unary with n, m, d^{k(1+b κ)}, χ^k, ⌈1/ε⌉, ⌈log₂(1/δ)⌉; reason: the paper names the primitive (Lemma 3.9, pp.38, 59), which runs in polynomial time; the unconditional statement implies the conditional one
--   - generalization: a tree-cut decomposition of width k ≥ 1 → of width at most k (k ≥ 1); reason: every bound is monotone in k; width exactly k is a special case
--   - generalization: (T̂, X̂) obtained after removing empty bags as in Lemma 6.13 → every tree-indexed partition satisfying Lemma 6.13's conclusions 1–2 for some decomposition of width ≤ k; reason: every outcome of the empty-bag removal satisfies them
--   - reading: tor(t) = |V(H̃_t)|, the size of the 3-centre of the torso → the least vertex count over all terminal results of the suppression process (tor); reason: the 3-centre is unique in the literature, so the values agree; the minimum makes the width hypothesis the weakest reading
--   - reading: (6.52) for the tree obtained from a computed decomposition of width k ≤ 2 tcw(G); the computation time 2^{O(tcw(G)² log tcw(G))} n² → a conjunct under k ≤ 2 tcw(G); the computation time is not stated; reason: the time bound is [Kim+18]'s, cited and not proved in the paper; (6.52) only uses k ≤ 2 tcw(G)
--   - encoding: O(·) bounds → one absolute constant C > 0 chosen before every instance parameter; reason: the base mission's reading of O(·); no constant depends on n, L, d, χ, w, k, ε or δ
--   - encoding: an algorithm receiving copies, ε and δ → one learner family (a Clifford+T circuit on qubit encodings of the copies plus ancillas, measured at the end) indexed by the instance with ⌈1/ε⌉ and ⌈log₂(1/δ)⌉; reason: the base mission's learner model; real ε ∈ (0, 1], δ ∈ (0, 1) remain the guarantee's parameters
--   - encoding: output a pure state with trace-norm error at most ε → the output decodes with the fixed decoder decodeTTN to a TTN whose normalised state is within trace norm ε of |ψ⟩⟨ψ|; reason: Gaussian-rational TTN entries cannot be exactly normalised; same guarantee
--   - encoding: b_T̂ after rooting as in Algorithm 6; κ; Δ(T̂) → leafBranching T̂; max 1 (Nat.clog d χ); T̂.maxDegree; reason: Algorithm 6 roots at a leaf (p.72); equal for d ≥ 2, χ ≥ 1
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.18, Eqs. (6.46)–(6.52), p.60; Lemma 6.13, p.55; Algorithm 6, p.72

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_prob
import Definitions.Def_AgnosticTNS_CopyLearner_code
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_AgnosticTNS_Supplement_encTCIndex
import Definitions.Def_AgnosticTNS_Supplement_tcw
import Definitions.Def_AgnosticTNS_Supplement_IsEmptyBagRemoval
import Definitions.Def_AgnosticTNS_leafBranching
import Definitions.Def_AgnosticTNS_Supplement_RealSuccess
import Definitions.Def_AgnosticTNS_TNSchi
open Matrix
open QAlgorithms.Complexity
open Classical

namespace AgnosticTNS.Supplement

/-- **Theorem 6.18 (Tomography using a tree-cut decomposition)**, p.60 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
Let `G = ([n], E)`, `(𝒯, X)` a tree-cut decomposition of `G` of width `k ≥ 1`, `(T̂, X̂)` obtained by removing
empty bags as in Lemma 6.13, `m = |V(T̂)|` (6.46); root `T̂` as in Algorithm 6 and let `b_T̂` be the maximum
number of children (6.47); `κ = max{1, ⌈log_d χ⌉}` (6.48). Then an unknown `|ψ⟩ ∈ S_d(G, χ)` can be learned
to trace-norm error at most `ϵ` with success probability at least `1 − δ` using
`O(m³/ϵ⁴ · (χ^k d^{k(1+b_T̂ κ)} + log(m/δ)))` copies (6.49). Consequently
`O(n³/ϵ⁴ · ((dχ)^{k max{2,Δ(T̂)}} + log(n/δ)))` copies suffice (6.50); if `m ≥ 3`,
`O(n³/ϵ⁴ · ((dχ)^{kΔ(T̂)} + log(n/δ)))` (6.51). For a computed decomposition of width `k ≤ 2 tcw(G)`, (6.50)
becomes `O(n³/ϵ⁴ · ((dχ)^{2 tcw(G) max{2,Δ(T̂)}} + log(n/δ)))` (6.52). The classical post-processing time,
after the decomposition has been chosen, is polynomial in `m, d^{k(1+b_T̂ κ)}, χ^k, 1/ϵ, log(1/δ)`.

**Formalization Note** "Of width `k`" is read as width at most `k`; the input is `(G, T̂, X̂, k, d, χ, ϵ, δ)`
with the hypothesis that some tree-cut decomposition of width `≤ k` yields `(T̂, X̂)` (`IsEmptyBagRemoval`,
Lemma 6.13 conclusions 1–2). `b_T̂ = leafBranching T̂` (Algorithm 6 roots at a leaf, p.72),
`Δ(T̂) = T̂.maxDegree`, `⌈log_d χ⌉ = Nat.clog d χ`. One learner family acting on the original `n` qudits,
one absolute constant, one polynomial-time printer of the Clifford+T circuit from the instance padded with
`n + m + d^{k(1+b_T̂ κ)} + χ^k + ⌈1/ϵ⌉ + ⌈log₂(1/δ)⌉`; the polynomial-time primitive assumption is
discharged (Lemma 3.9). Success is `RealSuccess` (4.1). The [Kim+18] computation time is cited and not
stated. -/
theorem theorem_6_18 :
    ∃ (Lr : CopyLearner TCIndex (fun i => i.n) (fun i => i.d)) (C : ℝ) (g : Str → Str),
      0 < C ∧ PolyTimeComputable g ∧
      ∀ (n d χ k m : ℕ) (G : SimpleGraph (Fin n)) (That : SimpleGraph (Fin m))
        (Xhat : Fin m → Finset (Fin n)) (ε δ : ℝ),
        1 ≤ k → 2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        (∃ D : TreeCutDecomp n, tcWidth G D ≤ k ∧ IsEmptyBagRemoval D That Xhat) →
        let b := leafBranching That
        let κ := max 1 (Nat.clog d χ)
        let i : TCIndex := ⟨n, G, m, That, Xhat, k, d, χ, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩
        g (encTCIndex i ++ unary (n + m + d ^ (k * (1 + b * κ)) + χ ^ k + ⌈1 / ε⌉₊ + ⌈Real.logb 2 (1 / δ)⌉₊)) = Lr.code i ∧
          (Lr.copies i : ℝ) ≤ C * (m : ℝ) ^ 3 / ε ^ 4 *
            ((χ : ℝ) ^ k * (d : ℝ) ^ (k * (1 + b * κ)) + Real.log (m / δ)) ∧
          (Lr.copies i : ℝ) ≤ C * (n : ℝ) ^ 3 / ε ^ 4 *
            (((d : ℝ) * χ) ^ (k * max 2 That.maxDegree) + Real.log (n / δ)) ∧
          (3 ≤ m → (Lr.copies i : ℝ) ≤ C * (n : ℝ) ^ 3 / ε ^ 4 *
            (((d : ℝ) * χ) ^ (k * That.maxDegree) + Real.log (n / δ))) ∧
          (k ≤ 2 * tcw G → (Lr.copies i : ℝ) ≤ C * (n : ℝ) ^ 3 / ε ^ 4 *
            (((d : ℝ) * χ) ^ (2 * tcw G * max 2 That.maxDegree) + Real.log (n / δ))) ∧
          ∀ ψ ∈ TNSchi d G χ, 1 - δ ≤ Lr.prob i (vecMulVec ψ (star ψ)) (RealSuccess ψ ε) := by sorry

end AgnosticTNS.Supplement
