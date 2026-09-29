-- Prove2me | Theorems.Thm_Deformation_ProartinianCat_exists_surjective_mvPowerSeriesLift
-- name    : Deformation.ProartinianCat.exists_surjective_mvPowerSeriesLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/e031fb80-7f8a-56ff-8ea2-5b323b8b32df
-- title:
--   Power series presentation of a pro-Artinian object
-- statement:
--   Let $\mathcal O$ be a commutative local Noetherian ring whose residue field $k = \mathcal O/\mathfrak m$ is finite and which is complete with respect to the $\mathfrak m$-adic filtration, and let $R$ be an object of the category [`Deformation.ProartinianCat 𝓞`](def/Deformations_ProartinianCat.html#L44), that is, a type carrying a commutative ring structure, a topology and an $\mathcal O$-algebra structure such that $R$ is a topological ring, a local ring, pro-Artinian, the structure map $\mathcal O \to R$ is a local homomorphism, and $R$ is a residue algebra over $\mathcal O$. Assume the tangent module [`Deformation.ProartinianCat.tangentSubmodule R`](def/Deformations_TangentSubmodule.html#L71) is a finite $k$-module; this is the $k$-submodule of $R \to k$ consisting of those $D$ that are additive, satisfy the Leibniz rule $D(rs) = \mathrm{res}(r)\,D(s) + D(r)\,\mathrm{res}(s)$ with respect to the residue map of $R$, vanish on the image of $\mathcal O$, and are locally constant. The assertion is that there exists a natural number $n$ with $n \le \dim_k$ of that tangent module, together with a morphism $f$ in [`Deformation.ProartinianCat 𝓞`](def/Deformations_ProartinianCat.html#L44) from [`Deformation.ProartinianCat.mvPowerSeriesObj 𝓞 n`](def/Deformations_MvPowerSeriesObj.html#L101) — the power series ring $\mathcal O[\![X_1,\dots,X_n]\!]$ in $n$ variables, topologised as a product of copies of $\mathcal O$ with its $\mathfrak m$-adic topology — to $R$, whose underlying ring homomorphism $f.\mathrm{hom}$ is surjective.
--
--   This is the classical presentation statement for complete local (pro-)Artinian algebras: an object of $\hat{\mathcal C}_{\mathcal O}$ with $d$-dimensional tangent space is a quotient of a power series ring over $\mathcal O$ in at most $d$ variables. It is used in assembling the data attached to a deformation ring, via [`GaloisRep.nonempty_deformationRingData`](thm.html#GaloisRep.nonempty_deformationRingData), where the tangent space bound is in turn fed by the embedding of the tangent space of a universal lifting ring into continuous cocycles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_ProartinianCat_exists_surjective_mvPowerSeriesLift.lean

import Mathlib
import Definitions.Def_Deformations_MvPowerSeriesObj
import Definitions.Def_Deformations_TangentSubmodule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory IsLocalRing

universe u v

theorem Deformation.ProartinianCat.exists_surjective_mvPowerSeriesLift {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
    [IsNoetherianRing 𝓞] [Finite (IsLocalRing.ResidueField 𝓞)] [IsAdicComplete (IsLocalRing.maximalIdeal 𝓞) 𝓞]
    (R : Deformation.ProartinianCat 𝓞)
    [Module.Finite (IsLocalRing.ResidueField 𝓞) (Deformation.ProartinianCat.tangentSubmodule R)] :
    ∃ n : ℕ, n ≤ Module.finrank (IsLocalRing.ResidueField 𝓞) (Deformation.ProartinianCat.tangentSubmodule R) ∧
      ∃ f : Deformation.ProartinianCat.mvPowerSeriesObj 𝓞 n ⟶ R, Function.Surjective f.hom := by sorry
