-- Prove2me | Theorems.Thm_CuspForm_exists_gamma0_apply_eq_eta_mul_pow_twentyfour
-- name    : CuspForm.exists_gamma0_apply_eq_eta_mul_pow_twentyfour
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/671719a8-48b0-5419-8716-07a0faae6ea4
-- title:
--   η(Nτ)²⁴ is a weight-12 cusp form on Γ₀(N)
-- statement:
--   Let $N$ be a natural number, assumed nonzero. The assertion is that there exists a cusp form $g$ of weight $12$ for the congruence subgroup $\Gamma_0(N)$ — an element of `CuspForm (CongruenceSubgroup.Gamma0 N) 12`, so a holomorphic function on the upper half-plane, weight-$12$ equivariant for $\Gamma_0(N)$ and with vanishing constant terms in its expansions at all cusps — whose values are given on the nose by the twenty-fourth power of the Dedekind eta function evaluated at $N$ times the argument: for every $\tau$ in the upper half-plane, $g(\tau) = \eta(N\tau)^{24}$, where $\eta$ is `ModularForm.eta` and $N\tau$ is the product of $N$ with the complex number underlying $\tau$. Since $\eta^{24} = \Delta$, the assertion is that $\tau \mapsto \Delta(N\tau)$ is a weight-$12$ cusp form of level $N$. The result is phrased purely existentially, so it names no distinguished element of $S_{12}(\Gamma_0(N))$; in particular it records that this space is nonzero for every $N \geq 1$.
--
--   This is the statement that the level-one discriminant form $\Delta$, pulled back along $\tau \mapsto N\tau$, lies in $S_{12}(\Gamma_0(N))$; it is obtained from the degeneracy map of [`CuspForm.exists_degeneracy_Gamma0`](thm.html#CuspForm.exists_degeneracy_Gamma0), which transports a cusp form of weight $k$ and level $M$ to level $N$ whenever $d M \mid N$, by composition with the action of the diagonal matrix attached to $d$, taken here with $M = 1$ and $d = N$. It underlies the constructions of eta products of level $4$ and level $11$ and the scaling identity for the twelfth power of the level-$11$ eta product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_gamma0_apply_eq_eta_mul_pow_twentyfour.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_gamma0_apply_eq_eta_mul_pow_twentyfour (N : ℕ) [NeZero N] :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 12,
      ∀ τ : UpperHalfPlane, g τ = ModularForm.eta (N * (τ : ℂ)) ^ 24 := by sorry
