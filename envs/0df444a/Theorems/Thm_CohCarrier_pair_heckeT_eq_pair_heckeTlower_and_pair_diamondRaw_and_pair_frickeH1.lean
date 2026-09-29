-- Prove2me | Theorems.Thm_CohCarrier_pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1
-- name    : CohCarrier.pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/aa1e197a-b522-56ca-8aba-10d9e48b9605
-- title:
--   Hecke adjointness, diamond and Fricke invariance of the cup pairing
-- statement:
--   Let $N$ be a nonzero natural number and $H \le (\mathbb{Z}/N)^{\times}$ a subgroup, and let $\Gamma =$ [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb{Z})$ of the subgroup of $\Gamma_0(N)$ consisting of the matrices whose lower-right entry reduces into $H$ under [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121). Let $\varphi, \psi \in$ [`CohCarrier.H1 N H ℚ`](def/CohCarrier_Level.html#L162), i.e. additive homomorphisms from $\Gamma$ (written additively) to $\mathbb{Q}$, and assume both are parabolic in the sense of [`ModularCurve.Period.IsParabolicHom`](def/ModularCurve_PeriodMap.html#L15): each vanishes on every $\gamma \in \Gamma$ whose integral matrix has trace squared equal to $4$. Write $\langle\cdot,\cdot\rangle$ for [`ModularCurve.CupPairing.pair`](def/ModularCurve_CupPairing.html#L18) $\Gamma$, defined (when $\Gamma$ has finite index and a primitive exists) as [`ModularCurve.PDPairing.cuspSum`](def/ModularCurve_PDPairing.html#L574) of a chosen function $h$ primitive for the antisymmetrised cocycle $\omega(\varphi,\psi)$, divided by $2\,\cdot$ `mult` $\Gamma$, with `mult` $\Gamma$ equal to $1$ if $-1 \in \Gamma$ and $2$ otherwise. The conclusion is a conjunction of three identities. First, for every nonzero natural number $q$, $\langle T_q\varphi, \psi\rangle = \langle \varphi, T_q^{\vee}\psi\rangle$, where $T_q =$ [`CohCarrier.heckeT N H q ℚ`](def/CohCarrier_Level.html#L250) is the transfer to $\Gamma$ of $\varphi$ composed with [`CohCarrier.conjL N H q`](def/CohCarrier_Level.html#L228) from `GammaHUpper N H q` into $\Gamma$, and $T_q^{\vee} =$ [`CohCarrier.heckeTlower N H q ℚ`](def/CohCarrier_Lower.html#L192) is the corresponding transfer along [`CohCarrier.conjLowerL N H q`](def/CohCarrier_Lower.html#L178) from `GammaHLower N H q`. Second, for every $\sigma \in \Gamma_0(N)$, the pairing is invariant under [`CohCarrier.diamondRaw N H ℚ σ`](def/CohCarrier_Level.html#L291), i.e. precomposition with $\gamma \mapsto \sigma\gamma\sigma^{-1}$, applied to both arguments. Third, the pairing is invariant under [`CohCarrier.frickeH1 N H ℚ`](def/CohCarrier_Fricke.html#L146), precomposition with the endomorphism [`CohCarrier.frickeHom N H`](def/CohCarrier_Fricke.html#L104) of $\Gamma$, applied to both arguments.
--
--   This is the adjointness of the double-coset operator $T_q$ with respect to the cup-product pairing on parabolic cohomology of $\Gamma_H(N)$ — its adjoint being the transposed, "lower", operator — together with the invariance of that pairing under the diamond conjugations by $\Gamma_0(N)$ and under the Fricke map. It is used in the construction of the perfect antisymmetric pairing on the relevant submodule of $H^1$ in the non-Eisenstein case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1.lean

import Mathlib
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Fricke
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_CupPairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (φ ψ : CohCarrier.H1 N H ℚ)
    (hφ : ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N H) φ)
    (hψ : ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N H) ψ) :
    (∀ (q : ℕ) [NeZero q],
      ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) (CohCarrier.heckeT N H q ℚ φ) ψ =
        ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) φ (CohCarrier.heckeTlower N H q ℚ ψ)) ∧
    (∀ σ : CongruenceSubgroup.Gamma0 N,
      ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) (CohCarrier.diamondRaw N H ℚ σ φ)
          (CohCarrier.diamondRaw N H ℚ σ ψ) =
        ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) φ ψ) ∧
    ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) (CohCarrier.frickeH1 N H ℚ φ)
        (CohCarrier.frickeH1 N H ℚ ψ) =
      ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) φ ψ := by sorry
