-- Prove2me | Theorems.Thm_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein
-- name    : CohCarrier.finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/28014bc7-a4af-5e52-bffa-7648e31ff47b
-- title:
--   Rank of a non-Eisenstein corner of H¹(Γ₀(N),𝒪)
-- statement:
--   Fix $N\ge 1$ and a finite set $S\subseteq\mathbb N$ containing no prime divisor of $N$, and let $\mathcal O$ be a discrete valuation domain of characteristic zero, complete for the adic topology of its maximal ideal, with residue field $k=\mathcal O/\mathfrak m$. The carrier is $H^1(N,\top,\mathcal O)=\operatorname{Hom}(\Gamma_{0}(N),\mathcal O)$, the additive homomorphisms from $\mathrm{GammaH}\,N\,\top=\Gamma_0(N)\le \mathrm{SL}(2,\mathbb Z)$ to $\mathcal O$, equipped with the operators [`CohCarrier.opFamily`](def/CohCarrier_Inst.html#L91) indexed by the generators [`CohCarrier.Gen`](def/CohCarrier_Inst.html#L13) $N$ $S$: $T_\ell$ for primes $\ell\notin S$ with $\ell\nmid N$, $U_q$ for primes $q\mid N$ (both given by the corestriction construction `heckeTL`), and $\langle d\rangle$ for $d\in(\mathbb Z/N)^\times$ (given by `diamondL`). It is assumed that these operators commute pairwise; $B$ denotes the $\mathcal O$-subalgebra of $\operatorname{End}_{\mathcal O}H^1(N,\top,\mathcal O)$ they generate, i.e. $\mathrm{Algebra.adjoin}$ of their range, attached to the Hecke datum with residue character $\bar\theta:\mathrm{Gen}\,N\,S\to k$. Let $\mathrm{Sp}$ be an [`IharaLemma.IdempotentSplitting`](def/IharaLemma_IdempotentSplitting.html#L7) of $B$: a complete family of orthogonal idempotents $e_1,\dots,e_n$ together with an enumeration $\mathfrak m_1,\dots,\mathfrak m_n$ of all maximal ideals of $B$ such that $e_i\in\mathfrak m_j$ exactly when $i\neq j$. Let $i_0$ be an index, write $e=e_{i_0}$ and let $\mathrm{CornerRing}\,i_0=eBe$ be the corresponding corner ring; suppose given an $\mathcal O$-algebra homomorphism $\pi_k:eBe\to k$ with $\pi_k(e\,\mathrm{op}(g)\,e)=\bar\theta(g)$ for every generator $g$. Assume the non-Eisenstein condition: there is a prime $\ell\notin S$ with $\ell\nmid N$, $\ell\equiv 1\pmod N$ and $\bar\theta(T_\ell)\neq \ell+1$ in $k$. Then the corner submodule $e\cdot H^1(N,\top,\mathcal O)$, the range of multiplication by $e$, satisfies $\operatorname{rank}_{\mathcal O}\big(e\,H^1(N,\top,\mathcal O)\big)=2\,\operatorname{rank}_{\mathcal O}(eBe)$, and for every $\mathcal O$-algebra homomorphism $\pi_C:eBe\to\mathcal O$ the submodule of $e\,H^1(N,\top,\mathcal O)$ annihilated by $\ker\pi_C$ has $\mathcal O$-rank $2$.
--
--   This is the pair of numerical conditions on a localised cohomological Hecke module — total rank twice the rank of the local Hecke algebra, and rank $2$ for the part cut out by an $\mathcal O$-valued character — which is what makes $H^1(\Gamma_0(N),\mathcal O)$ usable in the level-raising and lifting arguments; the non-Eisenstein hypothesis is what removes the boundary cohomology, on which $T_\ell$ acts by $\ell+1$ for $\ell\equiv 1\pmod N$. It is used by [`CohCarrier.free_sigmaCorner_gammaZero`](thm.html#CohCarrier.free_sigmaCorner_gammaZero), [`CohCarrier.torsionBySet_ne_bot_and_finrank_sigmaCornerSubmodule_auxLevel_eq_mul`](thm.html#CohCarrier.torsionBySet_ne_bot_and_finrank_sigmaCornerSubmodule_auxLevel_eq_mul) and [`CuspForm.AuxLevel.baseML_free_range_lsmul`](thm.html#CuspForm.AuxLevel.baseML_free_range_lsmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein.lean

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped IsMulCommutative in

theorem CohCarrier.finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein
    (N : ℕ) [NeZero N] (S : Set ℕ) (hSfin : S.Finite) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (hcomm : ∀ g h : CohCarrier.Gen N S,
      CohCarrier.opFamily N ⊤ S 𝒪 g * CohCarrier.opFamily N ⊤ S 𝒪 h =
        CohCarrier.opFamily N ⊤ S 𝒪 h * CohCarrier.opFamily N ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen N S → IsLocalRing.ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N S, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N), ℓ ≡ 1 [MOD N] ∧
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓN) ≠ (ℓ : IsLocalRing.ResidueField 𝒪) + 1) :
    Module.finrank 𝒪 ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)) =
      2 * Module.finrank 𝒪 (Sp.CornerRing i₀) ∧
    ∀ πC : Sp.CornerRing i₀ →ₐ[𝒪] 𝒪,
      Module.finrank 𝒪 ↥((Submodule.torsionBySet (Sp.CornerRing i₀)
          ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))
          ↑(RingHom.ker πC)).restrictScalars 𝒪) = 2 := by sorry
