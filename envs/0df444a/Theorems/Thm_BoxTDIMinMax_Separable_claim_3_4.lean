-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_claim_3_4
-- name    : BoxTDIMinMax.Separable.claim_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:54.935703+00:00
-- url     : https://prove2.me/theorems/5d2e06aa-9871-4e85-ab80-1e9a6244bb1a
-- title:
--   Claim 3.4, p. 14 (proof of Theorem 3.3) — at a Φ-minimizer z∗, ℓ(s) = φ′ₛ(z∗(s) − 1), u(s) = φ′ₛ(z∗(s)) satisfy (2.9)
-- statement:
--   Let $Q\in\mathbb Z^{I\times S}$, $p\in\mathbb Z^I$, let each $\varphi_s$ be discrete convex, $\Phi(z)=\sum_s\varphi_s(z(s))$, and assume $\Phi$ is finite-valued on $\ddot R$. Let $z^*\in\ddot R$ be a $\Phi$-minimizer: $\Phi(z^*)\le\Phi(z)$ for all $z\in\ddot R$. Define, for $s\in S$,
--   $$\ell(s):=\varphi_s'(z^*(s)-1)=\varphi_s(z^*(s))-\varphi_s(z^*(s)-1),\qquad u(s):=\varphi_s'(z^*(s))=\varphi_s(z^*(s)+1)-\varphi_s(z^*(s)),$$
--   where $\ell(s)$ may be $-\infty$ and $u(s)$ may be $+\infty$. Then
--   $$\tilde\ell(S^-)\le\tilde u(S^+) \qquad (2.9)$$
--   for every pair $(S^-,S^+)$ of disjoint subsets of $S$ with $z^*+\chi_{S^+}-\chi_{S^-}\in R$.
--
--   Combined with Theorem 2.12 this yields the dual vector $y^*$ of Theorem 3.3.
--
--   **Formalization Note** Box-TDI-ness is not assumed: the claim holds for every integral system. $\ell$, $u$ are the `lowerSlope`/`upperSlope` of the definitions file, evaluated where $\varphi_s(z^*(s))$ is finite.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 14, Claim 3.4 (in the proof of Theorem 3.3), definition of ℓ and u (p. 14)

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Claim 3.4, p. 14 (proof of Theorem 3.3): if `Φ` is finite on `R̈` and `z*` is a Φ-minimizer of
`R̈`, then with `ℓ(s) := φ'_s(z*(s) - 1)` and `u(s) := φ'_s(z*(s))` the inequality
`ℓ̃(S⁻) ≤ ũ(S⁺)` (2.9) holds for every pair of disjoint `S⁻, S⁺` with
`z* + χ_{S⁺} - χ_{S⁻} ∈ R`. -/
theorem claim_3_4 {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (phi : S → ℤ → WithTop ℤ) (hphi : ∀ s, DiscConvex (phi s))
    (Q : Matrix ι S ℤ) (p : ι → ℤ)
    (hfin : ∀ z ∈ intPts Q p, Phi phi z ≠ ⊤)
    (zStar : S → ℤ) (hz : zStar ∈ intPts Q p)
    (hmin : ∀ z ∈ intPts Q p, Phi phi zStar ≤ Phi phi z) :
    Cond29 Q p zStar (fun s => lowerSlope (phi s) (zStar s))
      (fun s => upperSlope (phi s) (zStar s)) := by sorry

end BoxTDIMinMax.Separable
