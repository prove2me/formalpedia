-- Prove2me | Theorems.Thm_Algebra_Etale_of_formallyUnramified_residueField_baseChange
-- name    : Algebra.Etale.of_formallyUnramified_residueField_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/92e012d0-56b9-54b9-b18a-eaed02bc6a43
-- title:
--   Finite flat with formally unramified residue fibre is étale
-- statement:
--   Let $R$ be a commutative local ring with residue field $k =$ `IsLocalRing.ResidueField R`, and let $S$ be a commutative $R$-algebra which is finite as an $R$-module and flat as an $R$-module. Assume that the base change $k \otimes_R S$ is formally unramified over $k$ in the sense of Mathlib's `Algebra.FormallyUnramified`, i.e. every $k$-algebra map from $k \otimes_R S$ into a quotient $A/I$ with $I^2 = 0$ has at most one lift to $A$ (equivalently, the module of Kähler differentials of $k \otimes_R S$ over $k$ vanishes). The conclusion is `Algebra.Etale R S`: the $R$-algebra $S$ is formally étale (unique lifting along nilpotent, indeed square-zero, extensions) and of finite presentation as an $R$-algebra. Note that finite presentation is part of the conclusion rather than a hypothesis: it is deduced from finiteness and flatness over the local base. No separability or Noetherian hypothesis is imposed, and the hypothesis on the fibre is only formal unramifiedness of $k \otimes_R S$ over $k$.
--
--   This is the fibre criterion for étaleness over a local base: for a finite flat algebra, étaleness may be tested on the special fibre. It is used in the construction of étale local algebras with prescribed residue field extension, in the analysis of quotients by base change along $R \to R/\mathfrak{m}$, and in the study of points of $p$-divisible groups with étale Cartier dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_of_formallyUnramified_residueField_baseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem Algebra.Etale.of_formallyUnramified_residueField_baseChange (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.Etale R S := by sorry
