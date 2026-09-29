-- Prove2me | Theorems.Thm_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le
-- name    : CohCarrier.exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/89f873ed-3484-57d5-8741-3e1349e0a411
-- title:
--   Steinberg-quotient eigensystem at level Nq, or Eisenstein
-- statement:
--   Let $N\ge 4$ be a nonzero natural number, $q$ a prime with $q\nmid N$, and $S_0$ a set of natural numbers. Let $\kappa$ be a field in which $q+1=0$ and $2\neq 0$, and let $V$ be a finite-dimensional $\kappa$-vector space carrying a representation $\rho$ of $\mathrm{GL}_2(\mathbb{Z}/q)$. Assume given a $\kappa$-linear map $\pi$ from the Steinberg submodule of $\kappa[\mathbb{P}^1(\mathbb{Z}/q)]$ — the kernel of the coefficient-sum map on [`CuspidalType.ProjLine q →₀ κ`](def/CuspidalType_IsCuspidalOfType.html#L21) — to $V$ which is equivariant for the natural $\mathrm{GL}_2(\mathbb{Z}/q)$-action, surjective, and whose kernel is exactly the line of multiples of the constant function [`CuspidalType.constFun`](def/CuspidalType_IsCuspidalOfType.html#L67); thus $V$ is the Steinberg representation modulo constants. Let $\lambda:\mathbb{N}\to\kappa$ and assume [`HeckeEis.IsEigensystemH1`](def/Gamma0CoeffCohomologyEigen.html#L72) holds for level $N$, the composite of $\rho$ with the reduction $\Gamma_0(N)\to \mathrm{SL}_2(\mathbb{Z})\to\mathrm{SL}_2(\mathbb{Z}/q)\to \mathrm{GL}_2(\mathbb{Z}/q)$, the twists $\rho(\mathrm{diag}(\ell,1))$ for $\ell\not\equiv 0 \bmod q$ (identity otherwise), the excluded set $\{q\}\cup S_0$ and the system $\lambda$: that is, there is a nonzero class in the coefficient cohomology `coeffH1` of that representation which, for every prime $\ell\nmid N$ outside $\{q\}\cup S_0$, is a $\lambda(\ell)$-eigenvector of some operator satisfying `IsCoeffHeckeOnH1` for $N$, $\ell$ and the given twist. The conclusion is a disjunction. Either there is a nonzero additive homomorphism $v$ from [`CohCarrier.GammaH (N*q) ⊥`](def/CohCarrier_Level.html#L133) — the subgroup of $\Gamma_0(Nq)$ killed by the diagonal-unit character, viewed additively — to $\kappa$ such that [`CohCarrier.diamondRaw`](def/CohCarrier_Level.html#L291) at $\sigma$, i.e. precomposition of $v$ with conjugation by $\sigma$, fixes $v$ for every $\sigma\in\Gamma_0(Nq)$, and [`CohCarrier.heckeT (N*q) ⊥ ℓ κ`](def/CohCarrier_Level.html#L250) (the transfer operator built from the conjugation map [`CohCarrier.conjL`](def/CohCarrier_Level.html#L228)) sends $v$ to $\lambda(\ell)\,v$ for every prime $\ell\nmid Nq$ with $\ell\notin S_0$; or else $\lambda$ is Eisenstein, $\lambda(\ell)=\ell+1$ in $\kappa$ for every prime $\ell\nmid N$ outside $\{q\}\cup S_0$.
--
--   This is the Diamond–Taylor dévissage of the induced representation $\kappa[\mathbb{P}^1(\mathbb{F}_q)]$ along $0\subset\kappa\subset\mathrm{St}$, combined with Shapiro's lemma, which transports an eigensystem occurring in the cohomology of $\Gamma_0(N)$ with coefficients in the Steinberg quotient into the setting of additive characters of the level-$Nq$ group equipped with its Hecke and diamond operators, the alternative being that the eigensystem is Eisenstein. It is used in the level-raising step feeding the construction of the mod-$\ell$ representation attached to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem CohCarrier.exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ)
    (hN4 : 4 ≤ N)
    (κ : Type) [Field κ] (hq1 : (q : κ) + 1 = 0) (h2 : (2 : κ) ≠ 0)
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
      π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)
    (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
      (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
      (insert q S₀) lam) :
    haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
    (∃ v : CohCarrier.H1 (N * q) ⊥ κ, v ≠ 0 ∧
      (∀ σ : CongruenceSubgroup.Gamma0 (N * q), CohCarrier.diamondRaw (N * q) ⊥ κ σ v = v) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * q → ℓ ∉ S₀ →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT (N * q) ⊥ ℓ κ v = lam ℓ • v) ∨
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (ℓ : κ) + 1 := by sorry
