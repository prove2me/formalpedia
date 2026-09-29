-- Prove2me | Theorems.Thm_CuspForm_petersson_heckeTLin
-- name    : CuspForm.petersson_heckeTLin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/b2a08ec9-dd85-5f7a-82a1-3f6c5afb0274
-- title:
--   Self-adjointness of Tₚ for the Petersson product at p ∤ N
-- statement:
--   Let $N$ be a natural number, $k$ an integer and $p$ a prime with $p \nmid N$, and let $f, g$ be cusp forms of weight $k$ for the congruence subgroup $\Gamma_0(N)$. Here [`CuspForm.heckeTLin k hp hpN`](def/ModularForm_HeckeOperatorForms.html#L69) is the $\mathbb{C}$-linear endomorphism of the space of weight-$k$ cusp forms on $\Gamma_0(N)$ whose underlying function on the upper half plane is $\mathrm{heckeT}\,k\,p\,f = \mathrm{heckeU}\,k\,p\,f + f \mid_k \mathrm{heckeDiagMatrix}\,p$, i.e. the $p$-th Hecke operator written as the sum of the $p$-fold $U$-type term and the weight-$k$ slash of $f$ by the diagonal matrix attached to $p$; and [`CuspForm.petersson f g`](def/CuspForm_Petersson.html#L20) is the Bochner integral over the standard fundamental domain `ModularGroup.fd` of $\mathrm{SL}_2(\mathbb{Z})$, with respect to Lebesgue measure restricted to that domain, of the function $\tau \mapsto \sum_{q \in \mathrm{SL}(2,\mathbb{Z})/\Gamma_0(N)} \mathrm{petersson}_k\,(f \mid_k q_{\mathrm{out}}^{-1})\,(g \mid_k q_{\mathrm{out}}^{-1})\,(\tau)$, the sum being a finite-support sum over the coset space taken along a choice of coset representatives, and no normalising volume or index factor being inserted. The assertion is that this pairing is self-adjoint for $T_p$: $\langle T_p f, g\rangle = \langle f, T_p g\rangle$.
--
--   This is the classical self-adjointness (Hermitian symmetry up to the conjugation built into the integrand) of the Hecke operator $T_p$ at a prime not dividing the level with respect to the Petersson inner product on $S_k(\Gamma_0(N))$. It is used in the project's treatment of newforms, for instance in the multiplicity-one statements that a newform is determined by its $q$-expansion coefficients and that a normalised eigenform is determined by its eigenvalues at primes away from the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_petersson_heckeTLin.lean

import Definitions.Def_CuspForm_Petersson
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.petersson_heckeTLin {N : ℕ} {k : ℤ} {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (CuspForm.heckeTLin k hp hpN f) g =
      CuspForm.petersson f (CuspForm.heckeTLin k hp hpN g) := by sorry
