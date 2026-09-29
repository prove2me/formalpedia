-- Prove2me | Theorems.Thm_AlgebraicCurve_carrier_hypotheses_of_endSlopes_of_nodePairs
-- name    : AlgebraicCurve.carrier_hypotheses_of_endSlopes_of_nodePairs
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/dffeccbd-a6cd-56cf-a0f4-acc1164d92d8
-- title:
--   Carrier hypotheses from end-slope data at node pairs
-- statement:
--   Let $F$ be a field equipped with an algebra structure over a field $k$, and let places of $F$ over $k$ be valuation subrings of $F$ containing $\mathrm{im}(k)$, proper, and principal ideal rings, with $v.\mathrm{ord}$ the associated integer-valued order function and $v.\mathrm{HasValue}\,g\,c$ meaning that $g$ lies in the valuation subring of $v$ and its residue equals the image of $c \in k$ in the residue field of $v$. Assume given: a non-empty finite set $S$ of pairs of places such that every first coordinate of a member of $S$ occurs as a second coordinate of a member of $S$ and conversely; a predicate $\mathrm{Fx}$ on places holding at both coordinates of every $s \in S$; finite sets $T_1, T_2$ of places at which $\mathrm{Fx}$ fails; functions $\bar E_1, \bar E_2, E_1, E_2$ from places to $\mathbb{Z}$ with $\bar E_i$ the indicator function of $T_i$ and $E_i \ge 0$; non-zero $u_1, u_2 \in F$ with $v.\mathrm{ord}\,u_i = E_i(v) - \bar E_i(v)$ at every place where $\mathrm{Fx}$ fails, with $v.\mathrm{ord}\,u_1 \ge 0$ at every place satisfying $\mathrm{Fx}$ that is not a first coordinate of a member of $S$, and with $v.\mathrm{ord}\,u_2 \ge 0$ at every place satisfying $\mathrm{Fx}$ that is not a second coordinate; a function $e$ on pairs of places with $e(s) \ge 1$ for $s \in S$, and a rational $\delta$ with $\delta \le e(s)\cdot s_1.\mathrm{ord}\,u_1$ and $-e(s)\cdot s_2.\mathrm{ord}\,u_2 \le \delta$ for all $s = (s_1,s_2) \in S$, and such that for $s \in S$, if $\delta = 0$ and $s_2.\mathrm{ord}\,u_2 = 0$ then $s_1.\mathrm{ord}\,u_1 = 0$ and there is $c \in k$ with $s_1.\mathrm{HasValue}\,u_1\,c$ and $s_2.\mathrm{HasValue}\,u_2\,c$; and two general-position hypotheses, namely that any $h \in F$ with $v.\mathrm{ord}\,h \ge 0$ off $T_1$, $v.\mathrm{ord}\,h \ge -1$ on $T_1$ and $w.\mathrm{HasValue}\,h\,0$ at every first coordinate $w$ of a member of $S$ is $0$, and that any $h \in F$ with $v.\mathrm{ord}\,h \ge 0$ off $T_2$ and $v.\mathrm{ord}\,h \ge -1$ on $T_2$ is the image of an element of $k$. The conclusion is that $v.\mathrm{ord}\,u_i \ge 0$ for all $v \notin T_i$ and $v.\mathrm{ord}\,u_i \ge -1$ for all $v \in T_i$, for $i = 1, 2$, and that for every $s = (s_1,s_2) \in S$ there is $c \in k$ with $s_1.\mathrm{HasValue}\,u_1\,c$ and $s_2.\mathrm{HasValue}\,u_2\,c$.
--
--   This is the passage from end-slope data along node pairs to the conditions that make a pair of rational functions a legitimate section on a glued curve: prescribed at most simple poles along the allowed sets $T_1, T_2$, regularity elsewhere, and matching values in $k$ at the two coordinates of each node. It is used in the study of specialisations of pinned charts on modular curves, where the divisors attached to the two sheets are compared after a twist vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_carrier_hypotheses_of_endSlopes_of_nodePairs.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open Classical in

theorem AlgebraicCurve.carrier_hypotheses_of_endSlopes_of_nodePairs
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (S : Finset (Place k F × Place k F)) (hSne : S.Nonempty)
    (hS₁₂ : ∀ s ∈ S, ∃ t ∈ S, t.2 = s.1) (hS₂₁ : ∀ s ∈ S, ∃ t ∈ S, t.1 = s.2)
    (Fx : Place k F → Prop) (hFx : ∀ s ∈ S, Fx s.1 ∧ Fx s.2)
    (T₁ T₂ : Finset (Place k F)) (hT₁ : ∀ v ∈ T₁, ¬ Fx v) (hT₂ : ∀ v ∈ T₂, ¬ Fx v)
    (Ebar₁ Ebar₂ EE₁ EE₂ : Place k F → ℤ)
    (hEbar₁ : ∀ v, Ebar₁ v = if v ∈ T₁ then 1 else 0) (hEbar₂ : ∀ v, Ebar₂ v = if v ∈ T₂ then 1 else 0)
    (hEE₁ : ∀ v, 0 ≤ EE₁ v) (hEE₂ : ∀ v, 0 ≤ EE₂ v)
    (u₁ u₂ : F) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (O1₁ : ∀ v, ¬ Fx v → (v.ord u₁ : ℤ) = EE₁ v - Ebar₁ v)
    (O1₂ : ∀ v, ¬ Fx v → (v.ord u₂ : ℤ) = EE₂ v - Ebar₂ v)
    (O2₁ : ∀ v, Fx v → (∀ s ∈ S, v ≠ s.1) → 0 ≤ v.ord u₁)
    (O2₂ : ∀ v, Fx v → (∀ s ∈ S, v ≠ s.2) → 0 ≤ v.ord u₂)
    (e : Place k F × Place k F → ℕ) (he : ∀ s ∈ S, 1 ≤ e s) (δ : ℚ)
    (A₁ : ∀ s ∈ S, δ ≤ (e s : ℚ) * ((s.1.ord u₁ : ℤ) : ℚ))
    (A₂ : ∀ s ∈ S, -((e s : ℚ) * ((s.2.ord u₂ : ℤ) : ℚ)) ≤ δ)
    (B : ∀ s ∈ S, δ = 0 → s.2.ord u₂ = 0 → s.1.ord u₁ = 0 ∧ ∃ c : k, s.1.HasValue u₁ c ∧ s.2.HasValue u₂ c)
    (hgp₁ : ∀ h : F, (∀ v, v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ S.image Prod.fst, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : F, (∀ v, v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : k, h = algebraMap k F c) :
    (∀ v, v ∉ T₁ → 0 ≤ v.ord u₁) ∧ (∀ v ∈ T₁, -1 ≤ v.ord u₁) ∧
    (∀ v, v ∉ T₂ → 0 ≤ v.ord u₂) ∧ (∀ v ∈ T₂, -1 ≤ v.ord u₂) ∧
    (∀ s ∈ S, ∃ c : k, s.1.HasValue u₁ c ∧ s.2.HasValue u₂ c) := by sorry
