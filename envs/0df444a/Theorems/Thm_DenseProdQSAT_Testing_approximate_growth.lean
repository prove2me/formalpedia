-- Prove2me | Theorems.Thm_DenseProdQSAT_Testing_approximate_growth
-- name    : DenseProdQSAT.Testing.approximate_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:19.900237+00:00
-- url     : https://prove2.me/theorems/c3510f82-353d-479a-9bd6-bfd07dcb3053
-- title:
--   Lemma 4.12 — growth of intermediate approximate ranges
-- statement:
--   For each positive local dimension $d$ there exists $C_d>0$, chosen before $k,\varepsilon,n,L$ and all instances and collections. Let $k\ge2$, $0<\varepsilon\le1$, $n\ge1$, and fix any family of valid support-associated collections of common positive size $L$. Put $N=Ld^{k-1}$. For each $1\le i\le J$, ordered support $F_t$ of distinct qudits with $0\le t\le4e^d/\tau_J$, and integer $m\ge1$,
--
--   $$\pi_{\mathcal R_{i,F_t}}(m)\le\bigl(C_d kN^{d+1}m\bigr)^{2dt}.$$
--
--   The family ranges over every compatible local assignment on that support. Tuples used in the actual growth function may repeat qudits. The case $t=0$ is included and gives growth at most one. The result supplies the finite combinatorial complexity needed by simultaneous hitting.
--
--   Differences from the source:
--   - encoding: tensor products on labels [n] and ordered supports → complex coordinate arrays on zero-based finite labels and lists of distinct labels; reason: canonical basis identification and relabeling preserve all assignments, dimensions, projectors and induced restrictions
--   - generalization: approximating collections selected by Lemma 4.11 with size given by Eq. (8) → arbitrary valid collections of any common positive length L; reason: the sign-count proof depends only on L and the subset sizes, not on accuracy or the formula choosing L; substituting the Lemma 4.11 collections gives every source instance
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Lemma 4.12, Eqs. (12)–(13), p. 16

import Definitions.Def_DenseProdQSAT_Testing_Approximation
set_option autoImplicit false

namespace DenseProdQSAT.Testing

theorem approximate_growth (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 2 ≤ k → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (n L : ℕ), 1 ≤ n → 1 ≤ L → ∀ (Φ : Instance n k d)
      (Q : CollectionFamily n k L) (i : ℕ), i ∈ Finset.Icc 1 (ScaleCount ε) →
      ∀ (F : List (Fin n)), F.Nodup →
        (F.length : ℝ) ≤ 4 * Real.exp d / Tau (ScaleCount ε) →
      ∀ (m : ℕ), 1 ≤ m →
        (Growth (ApproxRanges Φ Q F i) m : ℝ) ≤
          (C * k * (L * d ^ (k - 1) : ℕ) ^ (d + 1) * m) ^ (2 * d * F.length) := by sorry

end DenseProdQSAT.Testing
