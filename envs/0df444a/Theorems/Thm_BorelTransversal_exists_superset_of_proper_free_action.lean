-- Prove2me | Theorems.Thm_BorelTransversal_exists_superset_of_proper_free_action
-- name    : BorelTransversal.exists_superset_of_proper_free_action
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:14.461595+00:00
-- url     : https://prove2.me/theorems/2c782ab6-05ba-4f8e-8a44-2a1d7cdb074b
-- title:
--   Lemma A.5.2.10 — Borel fundamental domains for proper free actions of countable discrete groups: a Borel set meeting each orbit at most once extends to a Borel set meeting each orbit exactly once
-- statement:
--   **Existence of Borel fundamental domains (Borel transversals) extending a given partial one.** Let $X$ be a Hausdorff, locally compact, second countable topological space, equipped with its Borel $\sigma$-algebra. Let $H$ be a countable discrete abelian group acting on $X$ properly and freely; that is, the action $H\times X\to X$ is continuous, the map
--   $$H\times X\to X\times X,\qquad (h,x)\mapsto (h\cdot x,\,x)$$
--   is proper, and $h\cdot x=x$ for some $x\in X$ implies $h=e$. Let $q\colon X\to X/H$ be the quotient map onto the space of $H$-orbits.
--
--   Let $E\subset X$ be a Borel subset such that $q|_E\colon E\to X/H$ is injective, i.e. $E$ meets every $H$-orbit in at most one point. Then there exists a Borel subset $F\subset X$ such that
--   $$E\subset F\qquad\text{and}\qquad q|_F\colon F\to X/H\ \text{is a bijection},$$
--   i.e. $F$ meets every $H$-orbit in exactly one point.
--
--   Taking $E=\varnothing$ gives the existence of a Borel fundamental domain for the action. In the source the lemma is applied to a discrete subgroup $H$ of a second countable locally compact abelian group $G$ acting by translations (Remark A.5.2.7 and the proof of Proposition A.5.2.6): a Borel set $F\subset G$ containing a given $E$ and mapping bijectively onto $G/H$ computes the quotient Haar measure, $\mu_G(q^{-1}(A)\cap F)=\mu_{G/H}(A)$ for measurable $A\subset G/H$ (eq. (A.5.2.5)), which is how D-sequences are compared between $G$ and $G/H$.
--
--   **Deviation from the source.** The source prints "acting on $H$ properly and freely"; the group acts on $X$, as the quotient $X/H$ and the proof show.
--
--   **Formalization Note.** Properness of the action is Mathlib's `ProperSMul H X` (the map $(h,x)\mapsto(h\cdot x,x)$ is a proper map, which includes continuity of the action), freeness is the hypothesis `∀ h x, h • x = x → h = 1`, and $X/H$ is the quotient of $X$ by the orbit relation `MulAction.orbitRel H X`, with $q$ = `Quotient.mk`. Injectivity of $q|_E$ is `Set.InjOn q E`, and bijectivity of $q|_F\colon F\to X/H$ is `Set.BijOn q F Set.univ`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 572, Lemma A.5.2.10 (with Remark A.5.2.7, p. 571)

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace BorelTransversal

theorem exists_superset_of_proper_free_action (X H : Type*) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [CommGroup H] [TopologicalSpace H] [DiscreteTopology H] [Countable H]
    [MulAction H X] [ProperSMul H X] (hfree : ∀ (h : H) (x : X), h • x = x → h = 1)
    (E : Set X) (hE : MeasurableSet E)
    (hinj : Set.InjOn (Quotient.mk (MulAction.orbitRel H X)) E) :
    ∃ F : Set X, MeasurableSet F ∧ E ⊆ F ∧
      Set.BijOn (Quotient.mk (MulAction.orbitRel H X)) F Set.univ := by sorry

end BorelTransversal
