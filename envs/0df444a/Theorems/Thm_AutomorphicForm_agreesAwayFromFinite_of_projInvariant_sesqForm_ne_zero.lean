-- Prove2me | Theorems.Thm_AutomorphicForm_agreesAwayFromFinite_of_projInvariant_sesqForm_ne_zero
-- name    : AutomorphicForm.agreesAwayFromFinite_of_projInvariant_sesqForm_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/c2dac0c3-6698-5d79-a2b9-082111bc0d3f
-- title:
--   Agreement of Hecke eigensystems from an invariant pairing
-- statement:
--   Let $F$ be a number field, $D$ an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_F)$, and $\pi,\pi'$ complex Hecke eigensystems for $F$, each consisting of a non-zero level ideal of $\mathcal{O}_F$ together with functions $a,b$ on the finite places. Fix the carrier data assembled from $D$: the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, central subgroup $\top$, the level subgroups $N \mapsto \mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}(v)$, and the additive Haar measure conditioned on the adelic box. Let $R$, $R'$ be smooth cuspidal realizations over these data of the rescaled eigensystems $\pi^{\mathrm{raw}}$, $\pi'^{\mathrm{raw}}$ (in which $b(v)$ is divided by $\#(\mathcal{O}_F/v)$): that is, functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, not identically zero, smooth and cuspidal-automorphic with a central character, invariant under the level subgroup at the respective level, and, outside a finite exceptional set of places, eigenfunctions of the Hecke coset sum at $v$ with eigenvalue $a(v)$ and of translation by the central scalar $\det(\mathrm{heckeGen}(v))$ with eigenvalue $\#(\mathcal{O}_F/v)^{-1}b(v)$. Write $V$, $V'$ for the $\mathbb{C}$-spans of the right translates $z \mapsto R(zh)$, $z \mapsto R'(zh)$, $h \in \mathrm{GL}_2(\mathbb{A}_F)$. Let $P$ be a sesquilinear form on all functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$, linear in the first variable and conjugate-linear in the second, such that for each $g$ there is a scalar $c$ with $P(x(\cdot\, g), y(\cdot\, g)) = c\,P(x,y)$ for all $x \in V + V'$ and $y \in V'$. Assume some $y \in V'$ has $P(y,y) \neq 0$ and some $y \in V'$ has $P(R,y) \neq 0$. Then there is a finite set $S$ of finite places with $\pi'.a(v) = \pi.a(v)$ and $\pi'.b(v) = \pi.b(v)$ for all $v \notin S$.
--
--   This is the almost-everywhere form of strong multiplicity one used in the argument: a pairing between two cuspidal realizations that is invariant up to scalars under right translation, and non-degenerate in the two stated senses, forces the underlying Hecke eigensystems to have the same Hecke and central eigenvalues at all but finitely many finite places. It feeds the construction of a pair of eigensystems with meromorphic Euler-product $L$-series agreeing away from a finite set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_agreesAwayFromFinite_of_projInvariant_sesqForm_ne_zero.lean

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox

theorem AutomorphicForm.agreesAwayFromFinite_of_projInvariant_sesqForm_ne_zero
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (π π' : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π.toRawCentral)
    (R' : SmoothCuspRealizationAt F
      (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π'.toRawCentral)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ)
    (hP : ∀ g : AdelicGL2 (𝓞 F) F, ∃ c : ℂ, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) ⊔
          Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      P (fun z => x (z * g)) (fun z => y (z * g)) = c * P x y)
    (hself : ∃ y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      P y y ≠ 0)
    (hcross : ∃ y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      P R.toFun y ≠ 0) :
    HeckeEigensystem.AgreesAwayFromFinite π' π := by sorry
