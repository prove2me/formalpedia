-- Prove2me | Theorems.Thm_FormalGroup_exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot
-- name    : FormalGroup.exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/26bde53d-4fd6-59a0-88aa-bd82b914cc4c
-- title:
--   Rigidity: [q]_G is a homomorphism between square-zero lifts
-- statement:
--   Let $T$ and $k$ be commutative rings and $\pi : T \to k$ a ring homomorphism whose kernel $I$ satisfies $I^2 = 0$. Let $q$ be a natural number whose image in $T$ is zero. Let $F_0$ be a one-dimensional formal group law over $k$, and let $G_0$ and $G$ be one-dimensional formal group laws over $T$, with $G$ commutative, both lifting $F_0$ in the sense that $F_0$'s defining power series is the image of $G_0$'s, respectively of $G$'s, under the coefficientwise map induced by $\pi$. Write $[n]_G$ for the series defined recursively by $[0]_G = 0$ and $[n+1]_G = G([n]_G, X)$. Then there is a homomorphism $\theta$ from $G_0$ to $G$, that is, a power series over $T$ with zero constant term satisfying $\theta(G_0(X,Y)) = G(\theta(X), \theta(Y))$, whose underlying series is exactly $[q]_G$.
--
--   This is the rigidity statement for square-zero lifts: multiplication by $q$ on a commutative lift $G$ kills the deformation, so $[q]_G$ transports points from any other lift $G_0$ of the same reduction $F_0$ into $G$. It is used in the analysis of the $q$-series of a formal group, in particular in the construction of isomorphisms between lifts over a ring with square-zero maximal ideal and in the proof that $[q]_G$ is either zero or a unit times a power of $X$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem FormalGroup.exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot
    {T k : Type u} [CommRing T] [CommRing k] (π : T →+* k) (hπ : RingHom.ker π ^ 2 = ⊥)
    (q : ℕ) (hq : (q : T) = 0)
    (F₀ : FormalGroup k) (G₀ G : FormalGroup T) [G.IsComm]
    (hG₀ : G₀.IsBaseChange π F₀) (hG : G.IsBaseChange π F₀) :
    ∃ θ : FormalGroup.LawHom G₀ G, θ.series = G.nthSeries q := by sorry
