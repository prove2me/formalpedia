-- Prove2me | Theorems.Thm_DynChoiceJEO_Supplement_theorem_2
-- name    : DynChoiceJEO.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:13:05.550825+00:00
-- url     : https://prove2.me/theorems/d272d6d0-565d-549c-8e10-df55c457ad07
-- title:
--   Theorem 2 — the data errors $\epsilon^\circ+\epsilon^\bullet$ vanish when $p_t\to p$ and $\Theta_T\to\infty$
-- statement:
--   Let $X\subseteq\mathbb R^N$ and $Y\subseteq\mathbb R^k$, let the data vectors live in a real normed space with norm $\|\cdot\|$, let $\mathcal D$ be the parameter space in it, and let $\Psi(x,y;q)$ be a real function satisfying **Assumption 1** with constant $L_\Psi$:
--
--   $$
--   |\Psi(x,y;q)-\Psi(x,y;q')|\le L_\Psi\|q-q'\|\qquad(x\in X,\ y\in Y,\ q,q'\in\mathcal D).
--   $$
--
--   Let $x_t\in X$, $y_t\in Y$, $p_t\in\mathcal D$ and $\theta_t\ge0$ for $t\ge1$ be sequences with $\Theta_T=\sum_{t\in[T]}\theta_t\to\infty$, and let $p_t\to p\in\mathcal D$. For each horizon $T$ put
--
--   $$
--   \epsilon^\circ_T:=\sup_{y\in Y}\frac1{\Theta_T}\sum_{t\in[T]}\theta_t[\Psi(x_t,y;p)-\Psi(x_t,y;p_t)],\qquad
--   \epsilon^\bullet_T:=\sup_{x\in X}\frac1{\Theta_T}\sum_{t\in[T]}\theta_t[\Psi(x,y_t;p_t)-\Psi(x,y_t;p)].
--   $$
--
--   Then
--
--   1. the bounding sequence tends to zero,
--   $$
--   \lim_{T\to\infty}\frac{2L_\Psi}{\Theta_T}\sum_{t\in[T]}\theta_t\|p_t-p\|=0;
--   $$
--   2. the data errors are asymptotically at most this limit,
--   $$
--   \limsup_{T\to\infty}\,[\epsilon^\circ_T+\epsilon^\bullet_T]\le0 .
--   $$
--
--   The two data-error terms are the part of the saddle-point gap bound that the algorithm does not control; the theorem shows that they disappear when the estimates converge.
--
--   **Formalization Note** The limit superior is taken in the extended reals. The published definitions of the two errors are applied to the restrictions of the sequences to $[T]$, with $i\in\{0,\dots,T-1\}$ standing for $t=i+1$. Both suprema are finite by Assumption 1, so no boundedness hypothesis is added. Finitely many horizons with $\Theta_T=0$ do not affect either limit.
--
--   Differences from the source:
--
--   - generalization: §3 standing assumptions: X, Y convex compact, Ψ convex in x and concave in y → X, Y arbitrary sets and Ψ an arbitrary function satisfying Assumption 1; reason: the proof uses only Assumption 1; every instance of §3 is covered
--   - generalization: data vectors p with a fixed norm → an arbitrary real normed space P and a parameter space D ⊆ P, with Assumption 1, p and p_t on D; reason: specializes to ℝᵐ with any norm and any parameter space
--   - reading: sequences {x_t, y_t}, left implicit in the theorem → x_t ∈ X, y_t ∈ Y for every t ≥ 1, fixed independently of T; reason: step 2 of the framework (p.10) and the infinite sequences {x_t,y_t}_{t≥1} named on p.11
--   - encoding: index t ≥ 1 and [T] = {1,…,T} → sequences on ℕ with index 0 unused, restricted to Fin T by i ↦ i + 1; reason: reindexing; same sequences
--   - encoding: max over y ∈ Y and over x ∈ X in ε° and ε• → real sSup of the images (published epsCirc, epsBullet); reason: both images are nonempty and bounded by Assumption 1, so these are the suprema
--   - encoding: lim sup ≤ lim (2LΨ/Θ_T) Σ θ_t∥p_t − p∥ = 0 → Tendsto of that sequence to 0, and limsup in EReal ≤ 0; reason: the two clauses of the chain, without the junk value of a real limsup
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, Theorem 2, pp.11–12; Assumption 1, p.11; (11b)–(11c), p.11; proof, p.ec2 (PDF 24)

import Mathlib
import Definitions.Def_DynChoiceJEO_epsCirc
import Definitions.Def_DynChoiceJEO_epsBullet

open Filter Topology

namespace DynChoiceJEO.Supplement

/-- **Theorem 2: the data errors vanish.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*,
arXiv:1702.05702v5, Theorem 2, pp.11–12: "Suppose that Assumption 1 holds, and that {θ_t}_{t≥1} is chosen
so that θ_t ≥ 0 for all t ≥ 1, Θ_T = ∑_{t∈[T]} θ_t → ∞. Then, whenever p_t → p for any fixed p,
lim sup_{T→∞} [ϵ◦({x_t;p_t,θ_t}_{t∈[T]};p) + ϵ•({y_t;p_t,θ_t}_{t∈[T]};p)]
≤ lim_{T→∞} (2L_Ψ/Θ_T) ∑_{t∈[T]} θ_t‖p_t − p‖ = 0."
Assumption 1, p.11: "Fix a norm ‖·‖ on the data vectors p. There exists a constant L_Ψ < ∞ such
that for any (x,y) ∈ X × Y and data p,p′, we have |Ψ(x,y;p) − Ψ(x,y;p′)| ≤ L_Ψ‖p − p′‖."

**Formalization Note** The data vectors live in a real normed space `P`, and `D` is the parameter
space. The sequences are indexed by `t ≥ 1` (index `0` unused) and do not depend on `T`; the
published `epsCirc`, `epsBullet` are applied to their restrictions, `i : Fin T` standing for
`t = i + 1`. The conclusion has two clauses: the bounding sequence tends to `0`, and the limit
superior (in `EReal`) of `ε° + ε•` is at most that limit `0`. No boundedness hypothesis on the
suprema is needed, since Assumption 1 bounds both images. The standing convexity and compactness
assumptions of §3 are not used and are omitted. -/
theorem theorem_2 {N k : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (D : Set P) (X : Set (Fin N → ℝ)) (Y : Set (Fin k → ℝ))
    (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ) (LΨ : ℝ)
    (hLip : ∀ x ∈ X, ∀ y ∈ Y, ∀ q ∈ D, ∀ q' ∈ D, |Ψ x y q - Ψ x y q'| ≤ LΨ * ‖q - q'‖)
    (x : ℕ → Fin N → ℝ) (y : ℕ → Fin k → ℝ)
    (hx : ∀ t, 1 ≤ t → x t ∈ X) (hy : ∀ t, 1 ≤ t → y t ∈ Y)
    (θ : ℕ → ℝ) (hθ : ∀ t, 1 ≤ t → 0 ≤ θ t)
    (hΘ : Tendsto (fun T : ℕ => ∑ t ∈ Finset.Icc 1 T, θ t) atTop atTop)
    (pt : ℕ → P) (p : P) (hpt : ∀ t, 1 ≤ t → pt t ∈ D) (hp : p ∈ D)
    (hconv : Tendsto pt atTop (𝓝 p)) :
    Tendsto
        (fun T : ℕ => 2 * LΨ / (∑ t ∈ Finset.Icc 1 T, θ t) *
          ∑ t ∈ Finset.Icc 1 T, θ t * ‖pt t - p‖)
        atTop (𝓝 0) ∧
      limsup
        (fun T : ℕ =>
          ((DynChoiceJEO.epsCirc Ψ Y (fun i : Fin T => x (i + 1)) (fun i => pt (i + 1))
              (fun i => θ (i + 1)) p
            + DynChoiceJEO.epsBullet Ψ X (fun i : Fin T => y (i + 1)) (fun i => pt (i + 1))
              (fun i => θ (i + 1)) p : ℝ) : EReal))
        atTop ≤ 0 := by sorry

end DynChoiceJEO.Supplement
