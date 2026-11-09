-- Prove2me | Theorems.Thm_DenseProdQSAT_Testing_sample_complexity
-- name    : DenseProdQSAT.Testing.sample_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:58.48021+00:00
-- url     : https://prove2.me/theorems/e0bb394c-b568-4e20-a2c5-dc509ae1b5f5
-- title:
--   Theorem 1.3 / Theorem 3.3 — nearly linear canonical sample bound
-- statement:
--   For each positive integer $k$ and $d$, there exists $A_{k,d}>0$, independent of $\varepsilon,n$ and the instance. For every $0<\varepsilon\le1$ define
--
--   $$c=\left\lceil A_{k,d}\varepsilon^{-1}\log(2/\varepsilon)\right\rceil\ge1,\qquad s=\min\{n,c\}.$$
--
--   For every positive $n$ and arbitrary orthogonal-projector instance $\Phi$ on $n$ qudits of dimension $d$, draw a uniform unordered $s$-subset $C$. Accept exactly if the induced instance $\Phi[C]$ admits a normalized complex product-state solution. Then
--
--   $$\Phi\text{ product satisfiable}\ \Longrightarrow\ \Pr[\mathrm{accept}]=1,$$
--   $$\Phi\text{ is }\varepsilon\text{-far}\ \Longrightarrow\ \Pr[\mathrm{reject}]\ge\frac34.$$
--
--   Far-ness counts violated supports, at least $\varepsilon n^k$ for every normalized product assignment. For $n<c$ this is exact inspection. Thus the sample complexity in Definition 1.1 is $O_{k,d}(\varepsilon^{-1}\log(2/\varepsilon))$. Only the constant depends on $k,d$; states are not discretized and this is no runtime bound. The boundary cases $k=1$ and $d=1$ remain included.
--
--   Differences from the source:
--   - encoding: tensor products on labels [n] and ordered supports → complex coordinate arrays on zero-based finite labels and lists of distinct labels; reason: canonical basis identification and relabeling preserve all assignments, dimensions, projectors and induced restrictions
--   - encoding: the least sample complexity is O with a sufficiently large constant → a uniform positive constant followed by the canonical tester guarantee, its ceiling and min(n,c) exact-inspection branch; reason: this operational assertion gives the full stated bound without a possibly empty infimum
--   - generalization: the main proof invokes the k,d at least 2 regime of Lemma 3.2 → the operational theorem covers every positive k,d; reason: singleton constraints handle k=1 directly, and scalar projectors at d=1 embed as zero or identity projectors in dimension 2; all nontrivial source instances are retained
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Theorem 1.3; Theorem 3.3 and exact-inspection branch p. 6, p. 2

import Definitions.Def_DenseProdQSAT_Testing_Model
import Definitions.Def_DenseProdQSAT_Testing_FiniteRanges
set_option autoImplicit false

namespace DenseProdQSAT.Testing

theorem sample_complexity (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      1 ≤ SampleSize A ε ∧ ∀ (n : ℕ), 1 ≤ n → ∀ Φ : Instance n k d,
        (ProductSatisfiable Φ →
          SubsetProbability Finset.univ (min n (SampleSize A ε)) (Accepts Φ) = 1) ∧
        (EpsilonFar Φ ε →
          3 / 4 ≤ SubsetProbability Finset.univ (min n (SampleSize A ε))
            (fun C => ¬ Accepts Φ C)) := by sorry

end DenseProdQSAT.Testing
