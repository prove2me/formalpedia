-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional
-- name    : AlgebraicCurve.Place.finite_residueField_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/bbdfa1a3-22ad-54df-ab92-df7e9cd5811e
-- title:
--   Finiteness of residue degree in a finite extension
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the three structure maps forming a scalar tower $K \to F \to F'$, and assume $F'$ is finite-dimensional over $F$. Let $w$ be a place of $F'$ over $K$ in the sense of this project: a valuation subring $\mathcal{O}_w \subseteq F'$ containing $\mathrm{algebraMap}\,K\,F'(a)$ for every $a \in K$, different from the whole of $F'$, and which is a principal ideal ring. Write $w.\mathrm{ResidueField}$ for the residue field of the local ring $\mathcal{O}_w$, and let $w.\mathrm{restrict}\,F$ be the place of $F$ over $K$ whose valuation subring is the preimage $\mathcal{O}_w \cap F$ of $\mathcal{O}_w$ under $\mathrm{algebraMap}\,F\,F'$ (its three axioms being inherited from those of $w$). The conclusion is that $w.\mathrm{ResidueField}$ is a finite module over the residue field of $w.\mathrm{restrict}\,F$, the latter acting through the induced map of residue fields; equivalently, the residue degree $f(w \mid w|_F)$ is finite. No separability hypothesis on $F'/F$ is imposed.
--
--   This is the finiteness half of the classical statement that, in a finite extension of function fields, each place has finite residue degree; it is the separability-free form, and the bound obtained is by $[F':F]$. It is used in establishing that a field transcendental over $K$ gives a curve over $K$ in the project's sense, and in the degree bookkeeping for places on characteristic-$p$ fibre models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.finite_residueField_of_finiteDimensional {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] (w : Place K F') : Module.Finite (w.restrict F).ResidueField w.ResidueField := by sorry
