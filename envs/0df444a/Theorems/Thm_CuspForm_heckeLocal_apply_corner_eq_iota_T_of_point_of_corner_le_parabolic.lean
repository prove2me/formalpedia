-- Prove2me | Theorems.Thm_CuspForm_heckeLocal_apply_corner_eq_iota_T_of_point_of_corner_le_parabolic
-- name    : CuspForm.heckeLocal.apply_corner_eq_iota_T_of_point_of_corner_le_parabolic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/d3893228-60bc-5ddc-a141-dd1a6614184e
-- title:
--   Corner Tₚ at an 𝒪-point equals ι(aₚ(g))
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation domain of characteristic zero with finite residue field, let $p$ be a prime with $p \in \mathfrak m_{\mathcal O}$, let $S$ be a finite set of naturals containing $p$, let $N \ge 1$ satisfy $p \nmid N$ and have all its prime divisors in $S$, and let $r$ be a prime with $r \nmid Np$. Fix $H_0 \le (\mathbb Z/Nr)^\times$ together with the level datum `h₁₀` of type `LevelLE (N*r) (N*r) ⊤ H₀ 1`, giving the map `iDegL` from $H^1$ of $\Gamma_{\top}(Nr)$ to $H^1$ of $\Gamma_{H_0}(Nr)$ with $\mathcal O$-coefficients, where $H^1(M,H,A)$ denotes the additive homomorphisms $\mathrm{Additive}\,\Gamma_H(M) \to A$. Assume weight-$2$ cusp forms of level $N$ have an integral structure. Let $\theta_0 : \mathbb T_{N,2,S} \to \mathcal O/\mathfrak m$ be a ring homomorphism, $\mathbb T_{\theta_0} =$ `heckeLocal N S 𝒪 θ₀` the corresponding localisation, and $\pi_{T_0} : \mathbb T_{\theta_0} \to \mathcal O$ an $\mathcal O$-algebra map. Let $\mathbb T_0$ be a commutative $\mathcal O$-algebra acting on $H^1(Nr,H_0,\mathcal O)$ compatibly with $\mathcal O$, let $cd_0$ be corner data for this action (an idempotent splitting of $\mathbb T_0$, an index, and a level pairing between the corner ring and the corner submodule cut out by the chosen idempotent), and let $e_0$ be an $\mathcal O$-algebra isomorphism from $cd_0$'s corner ring onto $\mathbb T_{\theta_0}$. Assume: for every prime $\ell$ with $\ell \nmid N$, $\ell \notin S$, $\ell \nmid Nr$, the element $e_0^{-1}(\pi(T_\ell))$ acts on the corner module as `heckeT` at $\ell$; an element $t_p$ of the corner ring acts as `heckeT` at $p$; the submodule of the corner module annihilated by $\ker(\pi_{T_0} \circ e_0)$ is non-zero; and every class of the corner submodule lies in the image under `iDegL` of the parabolic homomorphisms `parabolicHoms 𝒪 (GammaH (N*r) ⊤) 𝒪`, those vanishing on all $\gamma$ with $(\operatorname{tr}\gamma)^2 = 4$. Finally let $M \ge 1$ with $M \mid N$ and $p \nmid M$, let $g$ be a newform of weight $2$ on $\Gamma_0(M)$ (a normalised eigenform with no good eigensystem at a proper divisor of $M$), let $\chi_g : \mathbb T_{M,2,S \setminus \{p\}} \to \mathbb C$ be a ring homomorphism with $\chi_g(T_\ell) = a_\ell(g)$ for all primes $\ell \nmid M$, $\ell \notin S \setminus \{p\}$, and let $\iota$ be a ring homomorphism from the range of $\chi_g$ to $\mathcal O$ with $\iota(\chi_g(T_\ell)) = \pi_{T_0}(\pi(T_\ell))$ for all primes $\ell \nmid N$, $\ell \notin S$. Then $\pi_{T_0}(e_0 t_p) = \iota(\chi_g(T_p))$.
--
--   This identifies the value at an $\mathcal O$-point of the corner element realising the Hecke operator at $p$ with the image under $\iota$ of the $p$-th coefficient $a_p(g)$ of the newform $g$ whose eigensystem the point interpolates away from $S$, in the variant where the eigen-corner is assumed to consist of classes pulled back from the parabolic cohomology of $\Gamma_{\top}(Nr)$. It feeds the analysis of the Hecke polynomial at $p$ in [`CuspForm.heckeLocal.sq_sub_apply_corner_mul_add_eq_zero_of_isOrdinaryAt_point_of_isUnit_of_corner_le_parabolic`](thm.html#CuspForm.heckeLocal.sq_sub_apply_corner_mul_add_eq_zero_of_isOrdinaryAt_point_of_isUnit_of_corner_le_parabolic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeLocal_apply_corner_eq_iota_T_of_point_of_corner_le_parabolic.lean

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing IharaLemma IharaTower
open CohCarrier

theorem CuspForm.heckeLocal.apply_corner_eq_iota_T_of_point_of_corner_le_parabolic
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (S : Finset ℕ) (hpS : p ∈ S)
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (r : ℕ) (hr : r.Prime) (hrN : ¬ r ∣ N * p) [NeZero (N * r)] (H₀ : Subgroup (ZMod (N * r))ˣ)
    (h₁₀ : LevelLE (N * r) (N * r) ⊤ H₀ 1)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ₀ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (πT₀ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀ →ₐ[𝒪] 𝒪)
    {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 (N * r) H₀ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 (N * r) H₀ 𝒪)]
    (cd₀ : H1CornerData (𝒪 := 𝒪) (N * r) H₀ 𝒪 𝕋₀)
    (e₀ : cd₀.cornerRing ≃ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀)
    (hT : ∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓr : ¬ ℓ ∣ N * r)
        (m : cd₀.cornerModule),
      ((e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • m
          : cd₀.cornerModule) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ ℓ 𝒪 (m : H1 (N * r) H₀ 𝒪))
    (tp : cd₀.cornerRing)
    (htp : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ∀ m : cd₀.cornerModule,
      ((tp • m : cd₀.cornerModule) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ p 𝒪 (m : H1 (N * r) H₀ 𝒪))
    (hocc : Submodule.torsionBySet cd₀.cornerRing cd₀.cornerModule ↑(RingHom.ker (πT₀.comp e₀.toAlgHom)) ≠ ⊥)
    (hW₀ : ∀ v : H1 (N * r) H₀ 𝒪, v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (cd₀.split.e cd₀.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH (N * r) ⊤) 𝒪).map (iDegL (N * r) (N * r) ⊤ H₀ 1 𝒪 𝒪 h₁₀))

    (M : ℕ) [NeZero M] (hMN : M ∣ N) (hpM : ¬ p ∣ M)
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hg : g.IsNewform)
    (chig : CuspForm.heckeAlgebra M 2 ((↑S : Set ℕ) \ {p}) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((↑S : Set ℕ) \ {p})),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (iota : chig.range →+* 𝒪)
    (hiota : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ
        (fun h => hℓN (h.trans hMN)) (fun h => hℓS (Set.mem_of_mem_diff h)))) =
        πT₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) :
    πT₀ (e₀ tp) =
      iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpM (fun h => h.2 rfl))) := by sorry
