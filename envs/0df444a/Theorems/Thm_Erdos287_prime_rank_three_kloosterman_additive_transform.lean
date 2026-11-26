-- Prove2me | Theorems.Thm_Erdos287_prime_rank_three_kloosterman_additive_transform
-- name    : Erdos287.prime_rank_three_kloosterman_additive_transform
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T20:45:56.72792+00:00
-- url     : https://prove2.me/theorems/9af9b341-8299-479f-8b5e-4ae13761a480
-- title:
--   Prime Fourier transform of the rank-three Kloosterman sum
-- statement:
--   At a prime $p$, let $K_3(x)=p^{-1}\sum_{uvw=x}e_p(u+v+w)$ on nonzero inputs. For a unit dilation $b$, the additive transform $\sum_{h\ne0}K_3(bh)e_p(-\ell h)$ is $-1/p$ at $\ell=0$. For $\ell\ne0$ it is the unnormalized rank-two Kloosterman sum $\sum_{u\ne0}e_p(u+(b/\ell)/u)$ minus $1/p$. The Lean statement clears the factor $p^{-1}$ and uses $t=\ell/b$, so its left side is the sum over three units.
-- source:
--   Erdős #287, the complete mean in mixed-residue Type III dispersion.

import Mathlib

theorem Erdos287.prime_rank_three_kloosterman_additive_transform (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    (∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ, ∑ w : (ZMod p)ˣ,
      ZMod.stdAddChar ((u : ZMod p) + (v : ZMod p) +
        (1 - t * (u : ZMod p) * (v : ZMod p)) * (w : ZMod p))) =
      (p : ℂ) * (if t = 0 then 0 else
        ∑ u : (ZMod p)ˣ, ZMod.stdAddChar ((u : ZMod p) + (t * (u : ZMod p))⁻¹)) - 1 := by sorry
