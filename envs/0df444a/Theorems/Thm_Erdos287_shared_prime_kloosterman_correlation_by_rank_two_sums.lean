-- Prove2me | Theorems.Thm_Erdos287_shared_prime_kloosterman_correlation_by_rank_two_sums
-- name    : Erdos287.shared_prime_kloosterman_correlation_by_rank_two_sums
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T20:53:20.355849+00:00
-- url     : https://prove2.me/theorems/96740e4b-4dcf-49f9-b759-b7d7b7f9fba6
-- title:
--   Shared-prime Kloosterman correlation by rank-two sums
-- statement:
--   At a prime $p$, let $K_3(x)=p^{-1}\sum_{uvw=x} e_p(u+v+w)$ for unit $x$, and let $S(c)=\sum_{u\ne0}e_p(u+c/u)$. For unit dilations $b_1,b_2$, $\sum_{h\ne0}K_3(b_1h)\overline{K_3(b_2h)}e_p(-th)$ equals $p^{-1}\sum_{\ell\ne0,t} S(b_1/\ell)\overline{S(b_2/(\ell-t))}-p^{-2}$. The formal statement clears $p^{-2}$ and uses the two sum distributions indexed by $b_i/(uv)$, so it also applies to arbitrary $b_i$ in that form.
-- source:
--   Erdős #287, mixed-residue Type III dispersion at a prime shared by both moduli.

import Mathlib

theorem Erdos287.shared_prime_kloosterman_correlation_by_rank_two_sums (p : ℕ) [Fact p.Prime] (b₁ b₂ t : ZMod p) :
    let U := (ZMod p)ˣ × (ZMod p)ˣ
    let σ : U → ZMod p := fun u => (u.1 : ZMod p) + (u.2 : ZMod p)
    let π : U → ZMod p := fun u => (u.1 : ZMod p) * (u.2 : ZMod p)
    let A : ZMod p → ℂ := fun ℓ =>
      ∑ u : U, if b₁ / π u = ℓ then ZMod.stdAddChar (σ u) else 0
    let B : ZMod p → ℂ := fun ℓ =>
      ∑ v : U, if b₂ / π v = ℓ then ZMod.stdAddChar (-σ v) else 0
    (∑ u : U, ∑ v : U, ∑ h : (ZMod p)ˣ,
      ZMod.stdAddChar (σ u - σ v + (b₁ / π u - b₂ / π v - t) * (h : ZMod p))) =
      (p : ℂ) * (∑ ℓ : ZMod p, A ℓ * B (ℓ - t)) - 1 := by sorry
