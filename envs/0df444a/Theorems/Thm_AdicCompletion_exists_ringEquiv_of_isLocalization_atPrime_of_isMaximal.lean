-- Prove2me | Theorems.Thm_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
-- name    : AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/1976b4a4-1429-5028-9486-72f7cd679f9b
-- title:
--   Completion at a maximal ideal commutes with localising there
-- statement:
--   Let $B$ and $S$ be commutative rings with $S$ a $B$-algebra, let $\mathfrak P \subseteq B$ be a maximal ideal, and assume $S$ is a local ring which is a localisation of $B$ at $\mathfrak P$, i.e. the structure map $B \to S$ realises $S$ as the localisation of $B$ at the multiplicative set $B \setminus \mathfrak P$ (`IsLocalization.AtPrime S 𝔓`). The assertion is that there exists a ring isomorphism $T$ from the $\mathfrak P$-adic completion `AdicCompletion 𝔓 B` of $B$ onto the $\mathfrak m_S$-adic completion `AdicCompletion (IsLocalRing.maximalIdeal S) S` of $S$, where $\mathfrak m_S$ is the maximal ideal of the local ring $S$, such that $T$ is compatible with the two structure maps from $B$: for every $b \in B$, applying $T$ to the image of $b$ under $B \to \widehat{B}_{\mathfrak P}$ gives the image of $b/1 \in S$ under $S \to \widehat{S}_{\mathfrak m_S}$. Only the existence of such a $T$ is asserted, not any particular construction of it; here the adic completions are Mathlib's inverse limits of the quotients by the powers of the respective ideals.
--
--   This is the standard identification $\widehat{B}_{\mathfrak P} \cong \widehat{B_{\mathfrak P}}$ for a maximal ideal $\mathfrak P$, packaged as a hypothesis-free existence statement together with its compatibility law over $B$, so that consumers may use the isomorphism as a black box. It is used to compare $\mathfrak P$-adic completions of a ring with completions of its local rings, for instance when identifying completed local rings of curves at closed points with rings of formal power series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
    {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    (𝔓 : Ideal B) [𝔓.IsMaximal] [IsLocalRing S] [IsLocalization.AtPrime S 𝔓] :
    ∃ T : AdicCompletion 𝔓 B ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ b : B, T (algebraMap B (AdicCompletion 𝔓 B) b)
        = algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap B S b) := by sorry
