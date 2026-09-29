-- Prove2me | Theorems.Thm_AutomorphicForm_orbitalIntegral_eq_shadow_of_irreducible_charpoly
-- name    : AutomorphicForm.orbitalIntegral_eq_shadow_of_irreducible_charpoly
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/5ecc66b0-b639-5545-9993-bbfd64ee77c1
-- title:
--   Elliptic orbital integral of a spherical Hecke function via its Satake shadow
-- statement:
--   Let $K$ be a number field, $v$ a finite place of $\mathcal{O}_K$, with completion $K_v$ and valuation ring $\mathcal{O}_v$, and let $\varpi \in \mathcal{O}_v$ be irreducible with nonzero image in $K_v$ and with $\mathcal{O}_v/(\varpi)$ finite of cardinality $q$. Write $U = \mathtt{LocalGL2.integralSubgroup}$, the image of $GL_2(\mathcal{O}_v)$ in $G = GL_2(K_v)$, and assume `hfin`: for every $g \in G$ the image of $U\{g\}$ in $G/U$ is finite. Let $\gamma \in G$ have irreducible characteristic polynomial, and let $\det \gamma = u\varpi^{D}$ with $u \in \mathcal{O}_v^{\times}$, $D \in \mathbb{Z}$. Let $S$ be a $\mathbb{C}$-algebra homomorphism from the Hecke algebra of bi-$U$-invariant $\mathbb{C}$-valued functions on $G$ with finite support modulo $U$ to $\mathbb{C}[\mathbb{Z}\times\mathbb{Z}]$ sending the indicator of the double coset of $\mathtt{diagPi}\,\varpi = \operatorname{diag}(\varpi,1)$ to $q\,X^{(1,0)} + X^{(0,1)}$, and that of the double coset of $\mathtt{diagPi}\,\varpi \cdot \mathtt{localRepInf}\,\varpi$ (the latter being $\mathtt{weylInt}\cdot\mathtt{diagPi}\,\varpi\cdot\mathtt{weylInt}$) to $X^{(1,1)}$. Let $T$ be the centraliser of $\{\gamma\}$ in $G$, equipped with its Borel structure, $\tau$ a Haar measure on $T$, and $T_c = T \cap \det^{-1}(\mathcal{O}_v^{\times})$. Assume the set of vertices of the tree fixed by $\gamma$ (over $\mathcal{O}_v$) is finite, that the relative index of $T_c \sqcup Z(G)$ in $T$ is nonzero, and that $\tau(T_c)$, as a real number, is nonzero. Finally let $f$ lie in the Hecke algebra and let $I \in \mathbb{C}$ be an orbital integral of $f$ at $\gamma$ against $\tau$ and the Haar measure on $G$ normalised to give $U$ mass $1$, i.e. $I = \int_G f(x^{-1}\gamma x) w(x)$ for some nonnegative measurable compactly supported $w$ with $\int_T w(tx)\,d\tau = 1$ whenever $f(x^{-1}\gamma x) \neq 0$. Then $I$ equals $([T : T_cZ]\cdot \tau(T_c))^{-1}$ times the sum of $C \cdot (Sf)_{(D/2,\,D/2)}$ if $D$ is even and $0$ otherwise, where $C$ is the number of vertices fixed by $\gamma$ and $D/2$ is integer division, plus twice the sum of the coefficients $(Sf)_{(a,b)}$ over pairs with $a < b$ and $a+b = D$.
--
--   This is the local computation, in the style of Langlands' analysis of orbital integrals of spherical functions for $GL_2$, expressing the elliptic orbital integral of a spherical Hecke operator in terms of the Satake-type image $Sf$ in $\mathbb{C}[\mathbb{Z}\times\mathbb{Z}]$ and of the number of vertices of the Bruhat–Tits tree fixed by $\gamma$. It is used in the construction of a Hecke algebra homomorphism matching local data at an inert prime, via [`AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime`](thm.html#AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_orbitalIntegral_eq_shadow_of_irreducible_charpoly.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LatticeTreeOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions Pointwise

theorem AutomorphicForm.orbitalIntegral_eq_shadow_of_irreducible_charpoly
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    [Finite ((v.adicCompletionIntegers K) ⧸ Ideal.span {ϖ})]
    (hfin : ∀ g : GL (Fin 2) (v.adicCompletion K),
      (QuotientGroup.mk '' ((LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) : Set (GL (Fin
          2) (v.adicCompletion K))) * {g}) :
        Set (GL (Fin 2) (v.adicCompletion K) ⧸ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion
            K))).Finite)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (u : (v.adicCompletionIntegers K)ˣ) (D : ℤ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u * algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K) ϖ ^ D)
    (S : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : S (HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖ hϖ0) (hfin _)) =
      (Nat.card ((v.adicCompletionIntegers K) ⧸ Ideal.span {ϖ}) : ℂ) • AddMonoidAlgebra.single ((1 : ℤ), (0 : ℤ)) 1 +
        AddMonoidAlgebra.single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : S (HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖ hϖ0 * LocalGL2.localRepInf ϖ hϖ0) (hfin _)) =
      AddMonoidAlgebra.single ((1 : ℤ), (1 : ℤ)) 1)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
        (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ)
    (hC : (LT.LatticeTree.fixedVertexSet (R := v.adicCompletionIntegers K) γ).Finite)
    (hTZ : ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
            Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
              (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range) ⊔
          Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex (Subgroup.centralizer ({γ} : Set (GL (Fin 2)
              (v.adicCompletion K)))) ≠ 0)
    (hm : (τ (((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
            Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
              (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range)).subgroupOf
            (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : Set (Subgroup.centralizer ({γ} : Set
                (GL (Fin 2) (v.adicCompletion K)))))).toReal ≠ 0)
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) (I :
        ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) I) :
    I = ((((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
            Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
              (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range) ⊔
              Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex (Subgroup.centralizer ({γ} : Set (GL (Fin 2)
                  (v.adicCompletion K)))) : ℂ) *
          ((τ (((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
            Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
              (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range)).subgroupOf
              (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : Set (Subgroup.centralizer ({γ} :
                  Set (GL (Fin 2) (v.adicCompletion K)))))).toReal : ℂ))⁻¹ *
      ((if Even D then (LT.LatticeTree.unitOrbitalCount (v.adicCompletionIntegers K) γ : ℂ) * (S f).coeff (D / 2, D /
          2) else 0) +
        2 * (S f).coeff.sum fun (x : ℤ × ℤ) (r : ℂ) => if x.1 < x.2 ∧ x.1 + x.2 = D then r else 0) := by sorry
