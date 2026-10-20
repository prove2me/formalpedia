-- Prove2me | Theorems.Thm_Esgk_sum_two_sub_witnesses_le
-- name    : Esgk.sum_two_sub_witnesses_le
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-20T05:16:13.868211+00:00
-- url     : https://prove2.me/theorems/ff3e0880-92ea-41a4-a61e-9f37c4257a9a
-- title:
--   Deficiency bound for equidistant witnesses with no three collinear points
-- statement:
--   Let $p=(p_1,\dots,p_n)$ be an injective configuration of $n$ points in the plane, with image $P=\{p_1,\dots,p_n\}$, and assume that no three points of $P$ are collinear. For indices $a\ne b$ let
--
--   $$
--   \alpha(a,b)=\#\{\,x\in\{1,\dots,n\}:\ |p_x-p_a|=|p_x-p_b|\,\}
--   $$
--
--   be the number of configuration points equidistant from $p_a$ and $p_b$. Let $D$ be the number of distinct values $|p_i-p_j|$ with $i\ne j$; since $p$ is injective, $D=D(P)$, the number of distinct distances determined by $P$. Then every set $\Phi$ of ordered pairs $(a,b)$ of distinct indices satisfies
--
--   $$
--   \sum_{(a,b)\in\Phi}\bigl(2-\alpha(a,b)\bigr)\le 2n\,(3D-n+1).
--   $$
--
--   The quantity $3D-n+1$ measures how far $D$ lies above $(n-1)/3$. In apex-counting arguments an upper bound for $\alpha$ on the pairs of $\Phi$ turns this inequality into an upper bound for $|\Phi|$.
--
--   **Formalization Note** $\alpha(a,b)$ is `(IndexedEquidistantWitnesses p a b).card` and $D$ is `NumDistancesOrdered p`. Indices are elements of `Fin n`, and the inequality is stated in the real numbers.
-- source:
--   Lean formalization by Adam McKenna (2026), declaration Esgk.sum_two_sub_witnesses_le.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_EquidistantWitnessCounts
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_PlanarGeneralPosition

open EuclideanGeometry Esgk

namespace Esgk

theorem sum_two_sub_witnesses_le {n : ℕ} {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    {Φ : Finset (Fin n × Fin n)} (hΦ : Φ ⊆ (Finset.univ : Finset (Fin n)).offDiag) :
    ∑ ab ∈ Φ, (2 - ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ)) ≤
      2 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) := by sorry

end Esgk
