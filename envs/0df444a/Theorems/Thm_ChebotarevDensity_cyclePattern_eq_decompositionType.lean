-- Prove2me | Theorems.Thm_ChebotarevDensity_cyclePattern_eq_decompositionType
-- name    : ChebotarevDensity.cyclePattern_eq_decompositionType
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:15:56.372181+00:00
-- url     : https://prove2.me/theorems/59df04b1-5706-49d2-819e-94e17ec47105
-- title:
--   The cycle pattern of σ_p equals the decomposition type of f mod p
-- statement:
--   Let $f\in\mathbb Z[X]$ be monic with discriminant $\Delta(f)\neq0$, with splitting field $K$ and Galois group $G$, and let $p$ be a prime with $p\nmid\Delta(f)$. If $\sigma\in G$ is a Frobenius substitution of $p$, then the cycle pattern of $\sigma$ as a permutation of the zeros of $f$ equals the decomposition type of $f$ modulo $p$:
--   $$\text{cycle pattern of }\sigma_p\;=\;\text{decomposition type of } f \bmod p .$$
--
--   Combined with Chebotarëv's theorem this yields Frobenius's theorem.
-- source:
--   P. Stevenhagen and H. W. Lenstra, Jr., "Chebotarëv and his density theorem", The Mathematical Intelligencer 18 (1996), no. 2, 26–37, https://doi.org/10.1007/BF03027290, p. 33: "Therefore, the cycle pattern of Frob_φ is indeed equal to the decomposition type of f modulo p."

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField

namespace ChebotarevDensity

theorem cyclePattern_eq_decompositionType (f : ℤ[X]) (hf : f.Monic) (hdisc : f.discr ≠ 0)
    (p : ℕ) [Fact p.Prime] (hpd : ¬ (p : ℤ) ∣ f.discr) (σ : GalGroup f)
    (hσ : IsFrobeniusAt f p σ) :
    cyclePattern f σ = decompositionType f p := by sorry

end ChebotarevDensity
