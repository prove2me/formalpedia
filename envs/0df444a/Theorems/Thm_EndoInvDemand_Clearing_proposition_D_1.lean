-- Prove2me | Theorems.Thm_EndoInvDemand_Clearing_proposition_D_1
-- name    : EndoInvDemand.Clearing.proposition_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:44.701064+00:00
-- url     : https://prove2.me/theorems/bacfd154-9542-4347-b800-2686f993ad6a
-- title:
--   Proposition D.1, p. 33 — z ↦ z exp(−R(𝒳 + z)) non-decreasing (concave) on ℝ₊₊ implies the same on 𝔻 − 𝒳
-- statement:
--   Let $R$ satisfy Assumption 3.1 on the domain $\mathbb D\in\{\mathbb R,\mathbb R_{++}\}$ and fix a number $x\in\mathbb D$. Consider
--   $$f(z)=z\exp(-R(x+z)),\qquad z\in\mathbb D-x=\{z\in\mathbb R \mid x+z\in\mathbb D\}.$$
--   1. If $f$ is non-decreasing on $\mathbb R_{++}$, then $f$ is non-decreasing on all of $\mathbb D-x$.
--   2. If $f$ is concave on $\mathbb R_{++}$, then $f$ is concave on all of $\mathbb D-x$.
--
--   Conditions (c) and (d) of Theorem 3.3 are imposed only for positive $z$; this proposition extends them to the whole domain of the map, which is what the uniqueness argument needs at negative arguments $z=Z-v$.
--
--   **Formalization Note** $x$ is a deterministic number ("for fixed $\mathcal X\in\mathbb D$"); $\mathbb D-x$ is written as $\{z \mid x+z\in\mathbb D\}$.
-- source:
--   Bichuch & Feinstein, Endogenous Inverse Demand Functions, arXiv:2012.08002v3, Proposition D.1 (Online Appendix D.2), p. 33

import Mathlib
import Definitions.Def_EndoInvDemand_Clearing_Setting
open MeasureTheory
open scoped ENNReal Topology

namespace EndoInvDemand.Clearing

/-- Proposition D.1, p. 33: if `z ∈ ℝ₊₊ ↦ z exp(−R(𝒳 + z))` is non-decreasing (concave) for a
fixed `𝒳 ∈ 𝔻`, then it is non-decreasing (concave) on its whole domain `𝔻 − 𝒳`. -/
theorem proposition_D_1 (D : Dom) (R : ℝ → ℝ) (hR : Assumption31 D R)
    (x : ℝ) (hx : x ∈ D.set) :
    (MonotoneOn (fun z => z * Real.exp (-R (x + z))) (Set.Ioi 0) →
        MonotoneOn (fun z => z * Real.exp (-R (x + z))) {z | x + z ∈ D.set}) ∧
    (ConcaveOn ℝ (Set.Ioi 0) (fun z => z * Real.exp (-R (x + z))) →
        ConcaveOn ℝ {z | x + z ∈ D.set} (fun z => z * Real.exp (-R (x + z)))) := by sorry

end EndoInvDemand.Clearing
