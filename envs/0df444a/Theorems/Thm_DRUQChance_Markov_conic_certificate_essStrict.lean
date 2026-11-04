-- Prove2me | Theorems.Thm_DRUQChance_Markov_conic_certificate_essStrict
-- name    : DRUQChance.Markov.conic_certificate_essStrict
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T00:04:45.91636+00:00
-- url     : https://prove2.me/theorems/4305b2ae-a73b-4962-8ddd-659a8f9fde26
-- title:
--   Refined conic duality — an inequality valid on an essentially strictly feasible conic set has a dual certificate
-- statement:
--   Let $C\in\mathbb R^{L\times P}$, $D\in\mathbb R^{L\times Q}$, $c\in\mathbb R^L$ and a cone $\mathcal K\subseteq\mathbb R^L$, and consider the conic set
--   $$\mathcal C=\{(z,u)\in\mathbb R^P\times\mathbb R^Q : Cz+Du\preccurlyeq_{\mathcal K} c\}.$$
--   Assume $\mathcal C$ is **essentially strictly feasible**: $\mathcal K=\{y: Gy\ge0\}\cap\mathcal K_n$ for a matrix $G$ (the polyhedral part) and a closed convex cone $\mathcal K_n$, and some $(z_0,u_0)$ has $c-Cz_0-Du_0\in\{y:Gy\ge0\}\cap\operatorname{int}\mathcal K_n$ (the non-polyhedral constraints hold strictly).
--
--   If the linear inequality $s^\top z\le t$ holds for every $(z,u)\in\mathcal C$, then it is certified by a dual vector: there is $\psi\in\mathcal K^\star$ with
--   $$C^\top\psi=s,\qquad D^\top\psi=0,\qquad c^\top\psi\le t .$$
--
--   This is the dual-attainment half of the refined conic duality theorem: the conic program $\sup\{s^\top z:(z,u)\in\mathcal C\}$ is essentially strictly feasible and bounded above by $t$, so its dual $\inf\{c^\top\psi:\psi\in\mathcal K^\star,\ C^\top\psi=s,\ D^\top\psi=0\}$ is solvable with value at most $t$. It is the step behind the case $\mathcal L=\emptyset$ of Theorem 7, where $\mathcal C_1$ lies inside $\{s^\top z\le t\}$ and (26) is solved with $\beta=0$, $\gamma=0$, $\phi=0$, $\tau=0$.
--
--   **Formalization note.** The cone and the conic set are the published `dualCone` and `confSet` from `DRConvexOpt.Reform.Setting`, and essential strict feasibility is `EssStrictFeas` from `DRUQChance.Markov.Basic`. No properness of $\mathcal K$ is assumed.
-- source:
--   Hanasusanto, Roitch, Kuhn & Wiesemann, A distributionally robust perspective on uncertainty quantification and chance constrained programming, Math. Program. 151(1) (2015): standing assumption of essential strict feasibility (footnote 1, p. 6), used for the case L = ∅ of Theorem 7 (p. 18, system (26)); the underlying result is the refined conic duality theorem (dual solvability for essentially strictly feasible, bounded conic programs), Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, §1.4.

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting
import Definitions.Def_DRUQChance_Markov_Basic

namespace DRUQChance.Markov

open Matrix DRConvexOpt.Reform

/-- Refined conic duality for an essentially strictly feasible confidence set: if the linear
inequality `sᵀ z ≤ t` holds on `{(z, u) : C z + D u ≼_K c}` and this set is essentially strictly
feasible, then it is certified by some `ψ ∈ K⋆` with `Cᵀψ = s`, `Dᵀψ = 0` and `cᵀψ ≤ t`. -/
theorem conic_certificate_essStrict {nP nQ m : ℕ} (C : Matrix (Fin m) (Fin nP) ℝ)
    (D : Matrix (Fin m) (Fin nQ) ℝ) (c : Fin m → ℝ) (K : Set (Fin m → ℝ))
    (hE : EssStrictFeas C D c K) (s : Fin nP → ℝ) (t : ℝ)
    (hst : ∀ ω ∈ confSet C D c K, s ⬝ᵥ ω.1 ≤ t) :
    ∃ ψ ∈ dualCone K, Cᵀ *ᵥ ψ = s ∧ Dᵀ *ᵥ ψ = 0 ∧ c ⬝ᵥ ψ ≤ t := by sorry

end DRUQChance.Markov
