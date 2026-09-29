-- Prove2me | Theorems.Thm_CohCarrier_heckeSym_top
-- name    : CohCarrier.heckeSym_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/6abce20f-b56c-5a98-8cbe-9158538db6a5
-- title:
--   Upper and lower Hecke operators agree at H=top
-- statement:
--   Let $M$ and $q$ be natural numbers, both nonzero, with $q$ prime and $q \nmid M$, let $V$ be an additive abelian group, and let $F$ be an element of `H1 M ⊤ V`, that is, an additive homomorphism from the additive group `Additive ↥(GammaH M ⊤)` to $V$; here `GammaH M ⊤` is the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ obtained by taking the preimage of the full subgroup $\top \le (\mathbb{Z}/M)^{\times}$ under `gamma0Units M` and pushing it forward along the inclusion of $\Gamma_0(M)$, so that $F$ is just a group homomorphism from $\Gamma_0(M)$ to $V$ (a $1$-cocycle for the trivial action). The conclusion is that the two endomorphisms of `H1 M ⊤ V` agree at $F$: the value `heckeTlower M ⊤ q V F`, obtained as the transfer of the homomorphism $F$ (read multiplicatively) precomputed with `conjLowerL M ⊤ q`, the conjugation map from `GammaHLower M ⊤ q` into `GammaH M ⊤` given by `conjLowerMat q`, equals `heckeT M ⊤ q V F`, the transfer of $F$ precomputed with `conjL M ⊤ q`, the conjugation map from `GammaHUpper M ⊤ q` into `GammaH M ⊤` given by `conjUpperMat q`. The assertion is pointwise in $F$ rather than an equality of the two additive maps.
--
--   This is the symmetry of the Hecke operator $T_q$ under transposition of the double coset $\Gamma_0(M)\,\mathrm{diag}(1,q)\,\Gamma_0(M) = \Gamma_0(M)\,\mathrm{diag}(q,1)\,\Gamma_0(M)$, here in the transfer-theoretic form used for the group cohomology carrier $H^1(\Gamma_0(M), V)$ with trivial coefficients. It is used in the derivation of the identities among the degree maps in [`CohCarrier.jDeg_iDeg_nine_identities_of_prime`](thm.html#CohCarrier.jDeg_iDeg_nine_identities_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeSym_top.lean

import Definitions.Def_CohCarrier_Lower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.heckeSym_top (M q : ℕ) [NeZero M] [NeZero q] (hq : q.Prime) (hqM : ¬ q ∣ M)
    {V : Type} [AddCommGroup V] (F : H1 M ⊤ V) :
    heckeTlower M ⊤ q V F = heckeT M ⊤ q V F := by sorry
