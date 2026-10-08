-- Prove2me | Theorems.Thm_DiffVI_Exist_prop_6_5
-- name    : DiffVI.Exist.prop_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:19.263748+00:00
-- url     : https://prove2.me/theorems/d2ac9edd-5ce5-44de-9491-d874badafbc7
-- title:
--   Proposition 6.5, pp. 38–39 — for F = D + Φ on a polyhedron: SOL(K, q + F) ≠ ∅ with (6.11); under (6.12), (6.13), (6.14) and convexity
-- statement:
--   Let $K\subseteq\mathbb R^m$ be a nonempty polyhedron containing either the origin or no lines. Let $D$ be a psd-plus $m\times m$ matrix such that $(K,D)$ is an R₀ pair, and let $\rho>0$ be such that (6.8) holds: for all $r\in\mathbb R^m$, $\mathrm{SOL}(K,r,D)\ne\emptyset$ and $\|u\|\le\rho(1+\|r\|)$ for $u\in\mathrm{SOL}(K,r,D)$. Let $\Phi:\mathbb R^m\to\mathbb R^m$ be continuous with
--   $$\|\Phi(u)\|\le L_\Phi\|u\|\quad\forall u\in K,\qquad(6.10)$$
--   for some $L_\Phi\in(0,1/\rho)$, and let $F=D+\Phi$. Then for every $q\in\mathbb R^m$, $\mathrm{SOL}(K,q+F)\neq\emptyset$ and
--   $$\sup\{\|u\|:u\in\mathrm{SOL}(K,q+F)\}\le\frac{\rho(1+\|q\|)}{1-\rho L_\Phi}.\qquad(6.11)$$
--   Assume in addition
--   $$\|\Phi(u)-\Phi(u')\|\le L'_\Phi\|Du-Du'\|\quad\forall u,u'\in K,\qquad(6.12)$$
--   for some $L'_\Phi\in(0,1/L_V)$, where $L_V>0$ is such that $\|Du^1-Du^2\|\le L_V\|r^1-r^2\|$ (6.9) for all $r^i\in\mathbb R^m$ and $u^i\in\mathrm{SOL}(K,r^i,D)$. Then
--   $$\|Du^1-Du^2\|\le\frac{L_V\|q^1-q^2\|}{1-L_VL'_\Phi}\qquad(6.13)$$
--   for all $q^i\in\mathbb R^m$ and $u^i\in\mathrm{SOL}(K,q^i+F)$; for every $q$ and every $\tilde u\in\mathrm{SOL}(K,q+F)$,
--   $$\mathrm{SOL}(K,q+F)=D^{-1}(D\tilde u)\cap\operatorname{argmin}\{u^T(q+F(\tilde u)):u\in K\};\qquad(6.14)$$
--   and consequently $\mathrm{SOL}(K,q+F)$ is convex.
--
--   This covers case (e) of Theorem 6.1, in which $F$ need not be monotone yet the VI solution sets remain convex and grow linearly.
--
--   **Formalization Note** $D^{-1}(D\tilde u)$ is the preimage of the point $D\tilde u$, and the argmin is the full set of minimizers of $u\mapsto u^T(q+F(\tilde u))$ over $K$. Nonemptiness of $K$ is the paper's standing assumption on VIs (p. 4); it also follows from (6.8).
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, pp. 38–39, Proposition 6.5, (6.8)–(6.14)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Exist_Setting

open MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace DiffVI.Exist

/-- Proposition 6.5, pp. 38–39: `K` a polyhedron containing the origin or no lines, `D` psd-plus
with `(K, D)` an R₀ pair, `ρ > 0` with (6.8), `Φ` continuous with (6.10) for `L_Φ ∈ (0, 1/ρ)`, and
`F = D + Φ`. Then `SOL(K, q + F) ≠ ∅` with the bound (6.11) for every `q`. If moreover (6.12)
holds with `L'_Φ ∈ (0, 1/L_V)`, where `L_V > 0` satisfies (6.9), then (6.13) holds, `SOL(K, q + F)`
has the representation (6.14), and it is convex. -/
theorem prop_6_5 {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hKne : K.Nonempty)
    (hKpoly : IsPolyhedron K)
    (hK0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ K ∨ ContainsNoLines K)
    (D : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hD : IsPSDPlus D)
    (hR0 : IsR0Pair K D)
    (ρ : ℝ) (hρ : 0 < ρ)
    (h68 : ∀ r : EuclideanSpace ℝ (Fin m),
      (SolodovSvaiterVI.Alg21.viSol (fun v => r + D v) K).Nonempty ∧
      ∀ u ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r + D v) K, ‖u‖ ≤ ρ * (1 + ‖r‖))
    (Φ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (hΦc : Continuous Φ)
    (LΦ : ℝ) (hLΦpos : 0 < LΦ) (hLΦlt : LΦ < 1 / ρ)
    (h610 : ∀ u ∈ K, ‖Φ u‖ ≤ LΦ * ‖u‖) :
    (∀ q : EuclideanSpace ℝ (Fin m),
      (SolodovSvaiterVI.Alg21.viSol (fun v => q + (D v + Φ v)) K).Nonempty ∧
      ∀ u ∈ SolodovSvaiterVI.Alg21.viSol (fun v => q + (D v + Φ v)) K,
        ‖u‖ ≤ ρ * (1 + ‖q‖) / (1 - ρ * LΦ)) ∧
    ∀ LV : ℝ, 0 < LV →
      (∀ r1 r2 : EuclideanSpace ℝ (Fin m),
        ∀ u1 ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r1 + D v) K,
        ∀ u2 ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r2 + D v) K,
          ‖D u1 - D u2‖ ≤ LV * ‖r1 - r2‖) →
    ∀ LΦ' : ℝ, 0 < LΦ' → LΦ' < 1 / LV →
      (∀ u ∈ K, ∀ u' ∈ K, ‖Φ u - Φ u'‖ ≤ LΦ' * ‖D u - D u'‖) →
      (∀ q1 q2 : EuclideanSpace ℝ (Fin m),
        ∀ u1 ∈ SolodovSvaiterVI.Alg21.viSol (fun v => q1 + (D v + Φ v)) K,
        ∀ u2 ∈ SolodovSvaiterVI.Alg21.viSol (fun v => q2 + (D v + Φ v)) K,
          ‖D u1 - D u2‖ ≤ LV * ‖q1 - q2‖ / (1 - LV * LΦ')) ∧
      (∀ q : EuclideanSpace ℝ (Fin m),
        ∀ ut ∈ SolodovSvaiterVI.Alg21.viSol (fun v => q + (D v + Φ v)) K,
          SolodovSvaiterVI.Alg21.viSol (fun v => q + (D v + Φ v)) K =
            (D ⁻¹' {D ut}) ∩
              {u | u ∈ K ∧ ∀ u' ∈ K, ⟪u, q + (D ut + Φ ut)⟫_ℝ ≤ ⟪u', q + (D ut + Φ ut)⟫_ℝ}) ∧
      (∀ q : EuclideanSpace ℝ (Fin m),
        Convex ℝ (SolodovSvaiterVI.Alg21.viSol (fun v => q + (D v + Φ v)) K)) := by sorry

end DiffVI.Exist
