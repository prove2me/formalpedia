-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_mem_of_isOpen_of_congruence
-- name    : AutomorphicForm.exists_forall_mem_of_isOpen_of_congruence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/c0dc8879-fc88-5388-afb5-765b8befd2be
-- title:
--   Open subgroups of GL₂(ℚₚ) contain a congruence subgroup
-- statement:
--   Let $p$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ and write $F = \mathbb{Q}_p$ for the adic completion of $\mathbb{Q}$ at $p$, carrying its valuation `Valued.v` with values in $\mathbb{Z}^{\ge}\cup\{0\}$ written multiplicatively as `WithZero (Multiplicative ℤ)`. Let $U$ be a subgroup of $GL_2(F)$ whose underlying set is open. Then there is a natural number $b$ with the following property: for every $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178) — that is, every $k \in GL_2(F)$ whose image under the monoid homomorphism [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97), which spreads $k$ out to a matrix over the finite adele ring of $\mathbb{Q}$, lies in `AdelicLevel.finiteLevelOne` for the unit ideal, so that both that image and the image of $k^{-1}$ satisfy the predicate `IsLevelOneMatrix` at the ideal $\top$ (in particular have integral entries) — if every entry of $k - 1$, with $k$ read as a matrix over $F$, has valuation at most `WithZero.exp (-(b : ℤ))`, then $k$ belongs to $U$.
--
--   This is the standard fact that the principal congruence subgroups of $GL_2(\mathbb{Z}_p)$ form a basis of neighbourhoods of the identity in $GL_2(\mathbb{Q}_p)$, in the shape of a uniform congruence level $b$ attached to a given open subgroup. It is used in the Rankin–Selberg part of the Langlands–Tunnell input, by [`LanglandsTunnell.RankinSelberg.forall_exists_rational_godementZeta2_whittaker_shift`](thm.html#LanglandsTunnell.RankinSelberg.forall_exists_rational_godementZeta2_whittaker_shift), to produce a congruence level at which prescribed local data is invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_mem_of_isOpen_of_congruence.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
  LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem AutomorphicForm.exists_forall_mem_of_isOpen_of_congruence
    (p : HeightOneSpectrum (𝓞 ℚ))
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hU : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ)))) :
    ∃ b : ℕ, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) - 1) i j) ≤
        WithZero.exp (-(b : ℤ))) → k ∈ U := by sorry
