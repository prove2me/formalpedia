-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_lemma_20
-- name    : DynEdgeColorLLL.Main.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:31.026863+00:00
-- url     : https://prove2.me/theorems/4ad92d23-0554-4830-91db-52b593eefbb6
-- title:
--   Lemma 20 — $\Pr[(w,a)\text{ is a critical failure}]\le e^{-\Omega(\tau_d)}$, also conditionally
-- statement:
--   Work in the regime of §5.1–§6, and fix an update of the edge $e=\{u,v\}$ turning $G^{old}$ into $G^{new}$, both of maximum degree at most $\Delta$. The directions and categories of the edges are independent and uniform. There is an absolute constant $c>0$ such that, for every vertex $w$ and every internal node $a$ of depth $d$,
--   $$\Pr\bigl[(w,a)\text{ is a critical failure}\bigr]\le e^{-c\,\tau_d}.$$
--   The bound remains valid after conditioning on three things: all randomness at levels smaller than $d$; the level-$d$ randomness of the edges not incident to $w$ in $\bar E^\cup_a=\bar E^{old}_a\cup\bar E^{new}_a$; and all randomness of the updated edge $e$.
--
--   This is the per-pair failure bound behind the shattering argument of Lemma 21.
--
--   **Formalization Note.** The conditional statement is given atom by atom. For every outcome $\omega_0$, among the outcomes agreeing with $\omega_0$ on the conditioned choices, the fraction where $(w,a)$ is a critical failure is at most $e^{-c\tau_d}$. The set $\bar E^\cup_a$ is determined by the choices at levels below $d$, so it is computed from $\omega_0$.
--
--   Differences from the source:
--   - reading: exp(−Ω(τ_d)) → exp(−c·τ_d) with c > 0 absolute; reason: the asymptotic notation with an explicit absolute constant
--   - encoding: the bound after conditioning on the listed randomness → for every outcome ω₀, the bound on the conditional frequency within the atom of outcomes agreeing with ω₀ on the conditioned coordinates; reason: on a finite uniform space this is conditioning on the generated σ-algebra, atom by atom
--   - encoding: independent uniform directions and categories of the edges at depths d < R → the uniform law on the finite space of choices of every vertex pair at every depth d < R; probabilities and expectations as normalized counts; reason: the choices of non-edges are independent of and irrelevant to the events, so the law of every event is unchanged
--   - reading: "Δ_ε large enough" and Δ > exp(Δ_ε) → an absolute D₀ with the statement for every real E ≥ D₀ and every Δ > exp(E); reason: the existential threshold is the meaning of "large enough"
--   - reading: log in q_d → log base 2; reason: same strength for either base
--   - encoding: conditioning on the level-d randomness of edges not incident to w in Ē∪_a → the atom also fixes the level-d choices of every vertex pair outside Ē∪_a; only the level-d choices of edges of Ē∪_a incident to w and the choices at levels above d are free; reason: the level-d choices of pairs outside Ē∪_a affect neither (w, a) nor (w, P(a)) being a seed failure, so the conditional bound is the same
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Lemma 20, printed p. 34 (PDF p. 36); Definition 7 and τ_d, printed p. 34 (PDF p. 36)

import Mathlib
import Definitions.Def_DynEdgeColorLLL_Main_Splitting
import Definitions.Def_DynEdgeColorLLL_Main_DynamicSplitting

namespace DynEdgeColorLLL.Main

open Classical in
/-- Lemma 20 (Peng–Ghaffari, STOC 2027 submission #615, printed p. 34, PDF p. 36). Fix an update
`G^old → G^new` (edge `e = {u, v}`) of graphs of maximum degree at most `Δ`, in the regime of
§5.1–§6, with independent uniform directions and categories. For every vertex `w` and every
internal node `a` of depth `d`, `Pr[(w, a) is a critical failure] ≤ exp(−Ω(τ_d))`; the bound
remains valid after conditioning on all randomness at levels smaller than `d`, on the level-`d`
randomness of edges not incident to `w` in `Ē^∪_a`, and on the randomness of `e`. -/
theorem lemma_20 :
    ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℝ, ∀ E : ℝ, D₀ ≤ E → ∀ Δ : ℕ, Real.exp E < Δ →
      ∀ {V : Type} [Fintype V] [DecidableEq V]
      (Gold Gnew : SimpleGraph V) (u v : V),
      IsEdgeUpdate Gold Gnew u v → (∀ x, Gold.degree x ≤ Δ) → (∀ x, Gnew.degree x ≤ Δ) →
      ∀ (w : V) (a : List Bool), a.length < depthR Δ E →
        randProb Δ E (fun ω : RandSpace V Δ E =>
            IsCriticalFailure Δ E Gold Gnew ω.toChoices (w, a)) ≤
          Real.exp (-(c * taud Δ a.length)) ∧
        ∀ ω₀ : RandSpace V Δ E,
          ((Finset.univ.filter fun ω : RandSpace V Δ E =>
              AgreeLemma20 Gold Gnew w a s(u, v) ω₀ ω ∧
                IsCriticalFailure Δ E Gold Gnew ω.toChoices (w, a)).card : ℝ) ≤
            Real.exp (-(c * taud Δ a.length)) *
              ((Finset.univ.filter fun ω : RandSpace V Δ E =>
                AgreeLemma20 Gold Gnew w a s(u, v) ω₀ ω).card : ℝ) := by sorry

end DynEdgeColorLLL.Main
