-- Prove2me | Theorems.Thm_DenseProdQSAT_Testing_uniform_approximation
-- name    : DenseProdQSAT.Testing.uniform_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:37.108001+00:00
-- url     : https://prove2.me/theorems/137b94b2-1117-4169-a999-20027b7ef1eb
-- title:
--   Lemma 4.11 — uniform absolute potential approximation
-- statement:
--   For every fixed $k\ge2$ and $d\ge1$, there exists $K_{k,d}>0$ independent of $\varepsilon,n,\Phi$ and the support. For every $0<\varepsilon\le1$, positive $n$, instance $\Phi$, and support $F$ with $|F|\le4e^d/\tau_J+1$, choose a single collection depending on $F$, of positive length
--
--   $$L=\left\lceil K_{k,d}\varepsilon^{-3}\log(2/\varepsilon)\right\rceil.$$
--
--   For every local assignment $A$ on this support, its corresponding approximate potential satisfies
--
--   $$|\widehat W_A-W_A|\le\frac{\varepsilon}{256}n^{k-1}.$$
--
--   The same collection works for every assignment state on the fixed ordered support. Empty summands contribute zero and repeated subsets are permitted. This supplies the approximating collections used in the intermediate range families.
--
--   Differences from the source:
--   - encoding: tensor products on labels [n] and ordered supports → complex coordinate arrays on zero-based finite labels and lists of distinct labels; reason: canonical basis identification and relabeling preserve all assignments, dimensions, projectors and induced restrictions
--   - encoding: a sufficiently large unspecified K and an approximating collection on F → a uniformly chosen positive K ensuring L is positive; reason: enlarging the unspecified constant ensures the average has positive length
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Lemma 4.11, Eqs. (8)–(9), p. 15

import Definitions.Def_DenseProdQSAT_Testing_Approximation
set_option autoImplicit false

namespace DenseProdQSAT.Testing

theorem uniform_approximation (k d : ℕ) (hk : 2 ≤ k) (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      1 ≤ ApproxSize K ε ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (Φ : Instance n k d)
      (F : List (Fin n)), F.Nodup →
      (F.length : ℝ) ≤ 4 * Real.exp d / Tau (ScaleCount ε) + 1 →
      ∃ Q : ApproximatingCollection n k (ApproxSize K ε) F.toFinset,
        ∀ ψ : States n d, IsLocal Φ F ψ →
          |ApproxPotential Φ F ψ Q - Potential Φ F ψ| ≤
            ε / 256 * (n : ℝ) ^ (k - 1) := by sorry

end DenseProdQSAT.Testing
