-- Prove2me | Theorems.Thm_FlowJobHardness_FlowShopGap_lemma_2_3
-- name    : FlowJobHardness.FlowShopGap.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:07.36998+00:00
-- url     : https://prove2.me/theorems/75104b50-292f-4939-b8c5-e743c1f19b4a
-- title:
--   Lemma 2.3 — for frequencies $k<\ell$, the sets $T_{g,k}$ and $T_{g,\ell}$ contain disjoint time intervals
-- statement:
--   Let $r\ge3$ and $d$ be natural numbers and let $s$ be a feasible schedule of the flow shop instance $F(r,d)$. Let $g\in\{1,\dots,r^{2d}\}$ be a machine group and let $k,\ell$ be frequencies with $1\le k<\ell\le d$. Then every interval of $T_{g,k}$ is disjoint from every interval of $T_{g,\ell}$:
--   $$I\cap J=\emptyset\qquad\text{for all } I\in T_{g,k},\ J\in T_{g,\ell}.$$
--   Here $T_{g,f}$ is the set of first halves $[s(o),s(o)+p(o)/2)$ of the good long-operations $o$ on machine $m_{g,f}$.
--
--   Together with the disjointness of operations on one machine, the lemma shows that the first halves of all good long-operations in one machine group are pairwise disjoint, so their total length is at most the makespan.
--
--   **Formalization Note** The paper's proof uses $r^{2(d-k)}/2-r^{2(d-\ell)}>\frac{r^2}{4}r^{2(d-\ell)}$, which holds for $r>2$; this is the threshold $r\ge3$. The lemma needs no assumption on the makespan.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:10, Lemma 2.3 (proof on pp. 20:10-20:11)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_FlowShopGap_Construction
import Definitions.Def_FlowJobHardness_FlowShopGap_GoodOps

open JobShopLTAS.Core

namespace FlowJobHardness.FlowShopGap

/-- Lemma 2.3 (p. 20:10): in every feasible schedule of `F(r, d)` (`r ≥ 3`), for every
machine group `g` and frequencies `1 ≤ k < ℓ ≤ d`, every interval of `T_{g,k}` is disjoint
from every interval of `T_{g,ℓ}`. -/
theorem lemma_2_3 (r d : ℕ) (hr : 3 ≤ r) (s : (inst r d).Op → ℝ)
    (hs : (inst r d).IsFeasibleSchedule Finset.univ s)
    (g : ℕ) (hg1 : 1 ≤ g) (hg2 : g ≤ r ^ (2 * d))
    (k ℓ : ℕ) (hk : 1 ≤ k) (hkℓ : k < ℓ) (hℓ : ℓ ≤ d) :
    ∀ I ∈ T r d s g k, ∀ J ∈ T r d s g ℓ, Disjoint I J := by sorry

end FlowJobHardness.FlowShopGap
