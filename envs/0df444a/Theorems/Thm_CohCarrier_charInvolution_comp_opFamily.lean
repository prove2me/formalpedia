-- Prove2me | Theorems.Thm_CohCarrier_charInvolution_comp_opFamily
-- name    : CohCarrier.charInvolution_comp_opFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/6864b0d8-40ea-5cdc-b2d6-b0eaf3ea72c8
-- title:
--   The character involution commutes with the Hecke generators
-- statement:
--   Fix a natural number $M$ that is nonzero, a subgroup $H \le (\mathbb{Z}/M)^\times$, a set $S$ of natural numbers, a commutative ring $\mathcal{O}$, and an element $g$ of the type [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) of Hecke generators, whose constructors are: `T ℓ` for a prime $\ell$ with $\ell \notin S$ and $\ell \nmid M$, `U q` for a prime $q$ dividing $M$, and `dia d` for a unit $d \in (\mathbb{Z}/M)^\times$. On the carrier $H^1(\Gamma_H(M), \mathcal{O})$ consider two $\mathcal{O}$-linear endomorphisms. The first is [`CohCarrier.charInvolution M H 𝒪 𝒪`](def/CohCarrier_CharInvolution.html#L43), taking an additive homomorphism $\varphi$ to its precomposition with the additive map induced by the endomorphism `jConjGammaH` of $\Gamma_H(M)$, which sends $\gamma$ to [`ModularCurve.Period.jConjSL`](def/ModularCurve_PeriodHomPair.html#L47) of $\gamma$ (conjugation by $\mathrm{diag}(1,-1)$, which preserves $\Gamma_H(M)$). The second is [`CohCarrier.opFamily M H S 𝒪 g`](def/CohCarrier_Inst.html#L91), which is `heckeTL M H 𝒪 ℓ` resp. `heckeTL M H 𝒪 q` on the constructors `T ℓ` and `U q` — the transfer `coresAdd` of the precomposition of $\varphi$ with the map induced by `conjL M H ℓ` — and `diamondL M H 𝒪 d` on `dia d`, namely the action `diamondRaw` of a chosen lift of $d$ to $\Gamma_0(M)$. The assertion is that these two endomorphisms commute.
--
--   This is the statement that the character involution induced by complex conjugation (the star involution on modular symbols) commutes with each generator of the Hecke action — the operators $T_\ell$, $U_q$ and the diamond operators $\langle d\rangle$ — on $H^1(\Gamma_H(M), \mathcal{O})$. It is used where the involution must be transported through the Hecke-module structure: in the construction of the Eichler–Shimura comparison for $\Gamma_H(M)$, in the identification of a corner submodule of $H^1$ with an eigenspace quotient under absolute irreducibility, and in the construction of the Galois-module pairing with the dual involving the involution and Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_charInvolution_comp_opFamily.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_CohCarrier_CharInvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.charInvolution_comp_opFamily
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] (g : CohCarrier.Gen M S) :
    CohCarrier.charInvolution M H 𝒪 𝒪 ∘ₗ CohCarrier.opFamily M H S 𝒪 g =
      CohCarrier.opFamily M H S 𝒪 g ∘ₗ CohCarrier.charInvolution M H 𝒪 𝒪 := by sorry
