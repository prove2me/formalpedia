-- Prove2me | Theorems.Thm_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section
-- name    : Algebra.FormallySmooth.exists_powerSeries_expansion_along_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/f6547afa-4409-5ac2-8cd7-80cfcc8c0f5f
-- title:
--   Power-series expansion along a formally smooth section
-- statement:
--   Let $R$ and $A$ be commutative rings with $A$ an $R$-algebra that is formally smooth over $R$, and let $e \colon A \to R$ be a homomorphism of $R$-algebras; write $I = \ker e$ for the kernel of the underlying ring homomorphism (so $e$ is a section of the structure map $R \to A$ with ideal $I$). Assume that the cotangent module $I/I^{2}$ is free as an $R$-module of rank $1$, i.e. its finite rank over $R$ equals $1$. The assertion is that there exists a ring homomorphism $\theta \colon A \to R[[t]]$ into the ring of formal power series over $R$ with three properties: (i) $\theta$ is $R$-linear in the sense that $\theta(r \cdot 1_{A}) = C(r)$, the constant power series, for every $r \in R$; (ii) for every $n \in \mathbb{N}$ and every $a \in A$, the coefficients of $\theta(a)$ in degrees $k < n$ all vanish if and only if $a \in I^{n}$; and (iii) for every $n \in \mathbb{N}$ and every $p \in R[[t]]$ there is an $a \in A$ with $\theta(a)$ and $p$ agreeing in all degrees $k < n$. Thus (ii) and (iii) say exactly that $\theta$ induces isomorphisms $A/I^{n} \cong R[[t]]/(t^{n})$ for all $n$.
--
--   This is the $t$-adic expansion along a smooth section: the completion of a formally smooth $R$-algebra along a section whose cotangent space is free of rank one is the power-series ring $R[[t]]$, as in EGA IV$_4$ §17.12. It is used, in the sharpened form [`Algebra.FormallySmooth.exists_powerSeries_expansion_along_section_apply_eq_X`](thm.html#Algebra.FormallySmooth.exists_powerSeries_expansion_along_section_apply_eq_X), to produce a formal parameter at a section, the expansion being normalised so that a chosen generator of $I$ is sent to $t$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Algebra.FormallySmooth.exists_powerSeries_expansion_along_section
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FormallySmooth R A]
    (e : A →ₐ[R] R) [Module.Free R (RingHom.ker e.toRingHom).Cotangent]
    (he : Module.finrank R (RingHom.ker e.toRingHom).Cotangent = 1) :
    ∃ θ : A →+* PowerSeries R,
      (∀ r : R, θ (algebraMap R A r) = PowerSeries.C r) ∧
      (∀ (n : ℕ) (a : A), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔
        a ∈ RingHom.ker e.toRingHom ^ n) ∧
      (∀ (n : ℕ) (p : PowerSeries R), ∃ a : A, ∀ k : ℕ, k < n →
        PowerSeries.coeff k (θ a) = PowerSeries.coeff k p) := by sorry
