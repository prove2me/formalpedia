-- Prove2me | Theorems.Thm_AlgebraicGeometry_isReduced_and_isClosed_or_mem_irreducibleComponents_and_infinite_of_openCover
-- name    : AlgebraicGeometry.isReduced_and_isClosed_or_mem_irreducibleComponents_and_infinite_of_openCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/26bc49c7-18ef-5b2c-ab88-3dae8fa301c2
-- title:
--   Reducedness, dimension ≤ 1 and infinite components from affine charts
-- statement:
--   Let $X$ be a scheme (in a fixed universe) whose underlying topological space is Jacobson, let $\iota$ be an index type, and let $R_i$ be commutative rings indexed by $i : \iota$. Suppose given morphisms $g_i : \operatorname{Spec} R_i \to X$, each an open immersion, such that the images of the underlying continuous maps cover $X$, i.e. every point of $X$ lies in the range of some $(g_i)_{\mathrm{base}}$. Assume further that each $R_i$ is a reduced ring; that each prime ideal $\mathfrak p$ of $R_i$ is either maximal or a minimal prime of $R_i$; and that for every minimal prime $\mathfrak p$ of $R_i$ the set of points $\mathfrak q$ of $\operatorname{Spec} R_i$ with $\mathfrak p \subseteq \mathfrak q$ is infinite. The conclusion is the conjunction of three assertions: $X$ is a reduced scheme; for every point $z$ of $X$, either the singleton $\{z\}$ is closed in $X$ or $\overline{\{z\}}$ is an irreducible component of $X$; and every irreducible component of $X$, as a subset of $X$, is infinite.
--
--   This is a criterion, checkable on an affine open cover, for a Jacobson scheme to be a reduced curve-like scheme: reduced, with every point either closed or generic for a component, and with all components infinite. It is used in the analysis of the special fibre of the Čerednik–Drinfeld / Mumford construction, being cited by [`CerednikDrinfeld.FormalOmega.MumfordGlue.specialLevel_isField_isReduced_dim_infinite`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlue.specialLevel_isField_isReduced_dim_infinite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isReduced_and_isClosed_or_mem_irreducibleComponents_and_infinite_of_openCover.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isReduced_and_isClosed_or_mem_irreducibleComponents_and_infinite_of_openCover
    (X : Scheme.{u}) [JacobsonSpace X]
    (ι : Type u) (R : ι → Type u) [∀ i, CommRing (R i)]
    (g : ∀ i, Spec (CommRingCat.of (R i)) ⟶ X) (hg : ∀ i, IsOpenImmersion (g i))
    (hcov : ∀ x : X, ∃ i, x ∈ Set.range (g i).base)
    (hred : ∀ i, _root_.IsReduced (R i))
    (hdim : ∀ i (p : Ideal (R i)), p.IsPrime → p.IsMaximal ∨ p ∈ minimalPrimes (R i))
    (hinf : ∀ i (p : Ideal (R i)), p ∈ minimalPrimes (R i) → Set.Infinite {q : PrimeSpectrum (R i) | p ≤ q.asIdeal}) :
    IsReduced X ∧
      (∀ z : X, IsClosed ({z} : Set X) ∨ closure ({z} : Set X) ∈ irreducibleComponents X) ∧
      (∀ C ∈ irreducibleComponents X, Set.Infinite C) := by sorry
