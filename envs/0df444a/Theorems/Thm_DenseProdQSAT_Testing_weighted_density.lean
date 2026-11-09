-- Prove2me | Theorems.Thm_DenseProdQSAT_Testing_weighted_density
-- name    : DenseProdQSAT.Testing.weighted_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:20.95276+00:00
-- url     : https://prove2.me/theorems/c92ad23c-5179-4d09-b367-b79d162f72e7
-- title:
--   Lemma 3.1 — weighted density of historical bad sets
-- statement:
--   Let $n,d\ge1$, $k\ge2$, and $0<\varepsilon\le1$. Let $\Phi$ be a quantum instance on $n$ qudits that is $\varepsilon$-far from product-state satisfiability. For every local assignment $A=(F,\psi)$, let $R_i(A)$ be its historical bad set, with $J=\lceil\log_2(16/\varepsilon)\rceil$ and $\tau_i=2^{-i}$. Then
--
--   $$\sum_{i=1}^J\tau_i|R_i(A)|\ge\frac{15\varepsilon n}{16}.$$
--
--   This supplies the weighted density used in the main testing theorem. The extension-space framework is used in its defined $k\ge2$ regime, and includes empty and fully assigned supports.
--
--   Differences from the source:
--   - encoding: tensor products on labels [n] and ordered supports → complex coordinate arrays on zero-based finite labels and lists of distinct labels; reason: canonical basis identification and relabeling preserve all assignments, dimensions, projectors and induced restrictions
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Lemma 3.1, p. 6

import Definitions.Def_DenseProdQSAT_Testing_Extension
set_option autoImplicit false

namespace DenseProdQSAT.Testing

theorem weighted_density {n k d : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) (hd : 1 ≤ d)
    (Φ : Instance n k d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfar : EpsilonFar Φ ε) (F : List (Fin n)) (ψ : States n d)
    (hA : IsLocal Φ F ψ) :
    15 * ε * n / 16 ≤ ∑ i ∈ Finset.Icc 1 (ScaleCount ε),
      Tau i * (BadSet Φ F ψ i).card := by sorry

end DenseProdQSAT.Testing
