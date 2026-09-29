-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_mapDomain_filter_apply_le_ord_of_sections
-- name    : AlgebraicCurve.Place.mapDomain_filter_apply_le_ord_of_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/17a15a66-be5a-59ab-a065-2f40289fbf9c
-- title:
--   Division by sections bounds a pushed-forward divisor by residue order
-- statement:
--   Let $K \subseteq F$ and $k \subseteq E$ be field extensions, and write $\mathrm{Place}\,K\,F$ for the places of $F$ over $K$, i.e. valuation subrings of $F$ that contain $\mathrm{algebraMap}\,K\,F$'s image, are proper, and are principal ideal rings; for such a place $W$ and $g \in F$, $W.\mathrm{ord}\,g$ is minus the logarithm of the value of $g$ under the associated height-one-spectrum valuation, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Let $\mathcal{O}$ be a valuation subring of $F$ and $\rho : \mathcal{O} \to E$ a ring homomorphism such that every $x \in \mathcal{O}$ with $\rho(x) \neq 0$ is a unit of $\mathcal{O}$. Let $r : \mathrm{Place}\,K\,F \to \mathrm{Place}\,k\,E$, let $S$ be a predicate on places of $F$, and let $v$ be a place of $E$. Assume (E): for every $g \in \mathcal{O}$ which satisfies $0 \le W.\mathrm{ord}\,g$ at every $W$ with $S\,W$ and $r\,W = v$, one has $0 \le v.\mathrm{ord}(\rho\,g)$; and (P): for every $Q$ with $S\,Q$ and $r\,Q = v$ there is $s \in \mathcal{O}$ with $Q.\mathrm{ord}\,s = 1$, $W.\mathrm{ord}\,s = 0$ for every other $W$ with $S\,W$ and $r\,W = v$, and $v.\mathrm{ord}(\rho\,s) = 1$. Let $f \in \mathcal{O}$ with $\rho(f) \neq 0$, and let $D$ be a divisor with $D\,W = W.\mathrm{ord}\,f$ for every place $W$ and $0 \le D\,W$ whenever $S\,W$ and $r\,W = v$. Then the value at $v$ of the pushforward along $r$ of the restriction of $D$ to $S$ — equivalently $\sum_{W \in \mathrm{supp}\,D,\ S\,W,\ r\,W = v} D\,W$ — is at most $v.\mathrm{ord}(\rho(f))$.
--
--   This is the general "division by sections" estimate underlying local semicontinuity statements for orders of vanishing under specialisation: the total order of $f$ along the selected places of $F$ lying over $v$ does not exceed the order of the residue $\rho(f)$ at $v$. It is applied with $\mathcal{O}$ a valuation ring of Gauss type and $\rho$ its residue map, and is cited in the analysis of the cusp at infinity on the model of the modular curve, through [`ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityInfty_prolongationDatum_of_residue`](thm.html#ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityInfty_prolongationDatum_of_residue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_mapDomain_filter_apply_le_ord_of_sections.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

open Classical in

theorem AlgebraicCurve.Place.mapDomain_filter_apply_le_ord_of_sections
    {K F : Type*} [Field K] [Field F] [Algebra K F] {k E : Type*} [Field k] [Field E] [Algebra k E]
    (𝒪 : ValuationSubring F) (ρ : 𝒪 →+* E)
    (hker : ∀ x : 𝒪, ρ x ≠ 0 → IsUnit x)
    (r : Place K F → Place k E) (S : Place K F → Prop) (v : Place k E)
    (hE : ∀ (f : F) (h : f ∈ 𝒪), (∀ W, S W → r W = v → 0 ≤ W.ord f) → 0 ≤ v.ord (ρ ⟨f, h⟩))
    (hP : ∀ Q, S Q → r Q = v → ∃ (s : F) (hs : s ∈ 𝒪),
      Q.ord s = 1 ∧ (∀ W, S W → r W = v → W ≠ Q → W.ord s = 0) ∧ v.ord (ρ ⟨s, hs⟩) = 1)
    (f : F) (h : f ∈ 𝒪) (hr : ρ ⟨f, h⟩ ≠ 0)
    (D : Divisor K F) (hD : ∀ W, D W = W.ord f)
    (hreg : ∀ W, S W → r W = v → 0 ≤ D W) :
    Finsupp.mapDomain r (D.filter S) v ≤ v.ord (ρ ⟨f, h⟩) := by sorry
