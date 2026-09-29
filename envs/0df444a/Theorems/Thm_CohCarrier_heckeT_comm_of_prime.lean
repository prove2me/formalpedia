-- Prove2me | Theorems.Thm_CohCarrier_heckeT_comm_of_prime
-- name    : CohCarrier.heckeT_comm_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/09e38ea6-cfb0-520e-895c-d20782ae12a6
-- title:
--   Hecke operators at coprime indices commute
-- statement:
--   Fix a natural number $M$, a subgroup $H \le (\mathbb{Z}/M\mathbb{Z})^{\times}$, and two nonzero natural numbers $\ell, \ell'$ with $\ell$ prime and $\gcd(\ell,\ell') = 1$. Let $V$ be an abelian group and let $F$ be an element of `H1 M H V`, that is, an additive homomorphism from $\Gamma_H(M)$, written additively, to $V$, where $\Gamma_H(M) =$ `GammaH M H` is the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ obtained by pulling back $H$ along the character `gamma0Units M` of $\Gamma_0(M)$ and pushing the result forward along the inclusion $\Gamma_0(M) \hookrightarrow \mathrm{SL}(2,\mathbb{Z})$; thus `H1 M H V` is $\mathrm{Hom}(\Gamma_H(M), V) = H^1(\Gamma_H(M), V)$ for the trivial action. For a nonzero $n$, the operator `heckeT M H n V` is the endomorphism of this group sending $\varphi$ to the transfer, from the subgroup `GammaHUpper M H n` up to $\Gamma_H(M)$, of the composite of the conjugation homomorphism `conjL M H n :` `GammaHUpper M H n` $\to \Gamma_H(M)$ with $\varphi$. The assertion is that these two operators commute on $F$: applying `heckeT M H ℓ V` after `heckeT M H ℓ' V` gives the same homomorphism as applying them in the opposite order. No hypothesis relating $\ell$ or $\ell'$ to the level $M$ is imposed, so either index may divide $M$.
--
--   This is the commutativity of the Hecke operators $T_\ell$ and $T_{\ell'}$ at coprime indices on the first cohomology of $\Gamma_H(M)$ with trivial coefficients, in the transfer (double coset) description of the operators; note the asymmetry of the hypotheses, only $\ell$ being required to be prime. It underlies the later simultaneous-eigenvector and eigenvalue arguments for the Hecke action on these cohomology groups, which invoke it in the form stated here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_comm_of_prime.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.heckeT_comm_of_prime (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (hℓ : ℓ.Prime) (hcop : Nat.Coprime ℓ ℓ') {V : Type} [AddCommGroup V] (F : H1 M H V) :
    heckeT M H ℓ V (heckeT M H ℓ' V F) = heckeT M H ℓ' V (heckeT M H ℓ V F) := by sorry
