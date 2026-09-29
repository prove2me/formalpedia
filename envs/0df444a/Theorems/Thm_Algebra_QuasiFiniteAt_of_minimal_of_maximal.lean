-- Prove2me | Theorems.Thm_Algebra_QuasiFiniteAt_of_minimal_of_maximal
-- name    : Algebra.QuasiFiniteAt.of_minimal_of_maximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/f924fc28-0da3-5f7d-87e0-cd0110f8d007
-- title:
--   Quasi-finiteness at an isolated point of its fibre
-- statement:
--   Let $R$ and $S$ be commutative rings and let $S$ be an $R$-algebra which is of finite type (`Algebra.FiniteType R S`), and let $\mathfrak q \subset S$ be a prime ideal. Write $\mathfrak p = \mathfrak q \cap R$ for the contraction of $\mathfrak q$ along the structure map $R \to S$, i.e. the comap of $\mathfrak q$ under `algebraMap R S`. Consider the property of an ideal $P \subset S$ of being prime with contraction to $R$ equal to $\mathfrak p$. Assume two hypotheses: $\mathfrak q$ has this property and is minimal for it, in the sense that any prime $P \subset S$ with $P \subset \mathfrak q$ and $P \cap R = \mathfrak p$ satisfies $\mathfrak q \subset P$; and $\mathfrak q$ has this property and is maximal for it, in the sense that any prime $P \supset \mathfrak q$ with $P \cap R = \mathfrak p$ satisfies $P \subset \mathfrak q$. The conclusion is `Algebra.QuasiFiniteAt R 𝔮`: the $R$-algebra $S$ is quasi-finite at $\mathfrak q$.
--
--   This is the standard order-theoretic criterion for quasi-finiteness of a finite-type algebra at a prime: no prime of the fibre over $\mathfrak p$ lies strictly below or strictly above $\mathfrak q$, i.e. $\mathfrak q$ is an isolated point of its fibre. It is the form in which quasi-finiteness is verified in the scheme-theoretic part of the development, where it feeds into the identification of local rings of curves (normal or nodal affine models) with localisations of their coordinate rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_QuasiFiniteAt_of_minimal_of_maximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.QuasiFiniteAt.of_minimal_of_maximal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (𝔮 : Ideal S) [𝔮.IsPrime]
    (hmin : Minimal
      (fun P : Ideal S => P.IsPrime ∧ P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S)) 𝔮)
    (hmax : Maximal
      (fun P : Ideal S => P.IsPrime ∧ P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S)) 𝔮) :
    Algebra.QuasiFiniteAt R 𝔮 := by sorry
