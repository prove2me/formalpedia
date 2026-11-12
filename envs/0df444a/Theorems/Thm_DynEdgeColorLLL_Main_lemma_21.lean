-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_lemma_21
-- name    : DynEdgeColorLLL.Main.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:34.371176+00:00
-- url     : https://prove2.me/theorems/33eb8471-267d-44a4-b060-e73552b90c22
-- title:
--   Lemma 21 — $\mathbb E\,|\{\langle x,b\rangle\in\hat K(\langle w,a\rangle):\mathrm{dep}(b)=d\}|\le e^{-\Omega(\tau_d+\tau_{\mathrm{dep}(a)})}$
-- statement:
--   Work in the regime of §5.1–§6, and fix an update of the edge $e=\{u,v\}$ turning $G^{old}$ into $G^{new}$, both of maximum degree at most $\Delta$. The directions and categories of the edges are independent and uniform. There is an absolute constant $c>0$ such that, for every vertex $w$, every internal node $a$ of $T$ and every $0\le d<R$,
--   $$\mathbb E\Bigl[\bigl|\{\langle x,b\rangle\in\hat K(\langle w,a\rangle):\mathrm{dep}(b)=d\}\bigr|\Bigr]\le e^{-c(\tau_d+\tau_{\mathrm{dep}(a)})},$$
--   where $\hat K(\langle w,a\rangle)$ is the component of $\langle w,a\rangle$ in the graph $\hat G$ of Definition 8 (empty if $\langle w,a\rangle\notin\hat V$). The same bound holds after conditioning on all random choices of the updated edge $e$.
--
--   This shattering bound controls the expected work of both the failure discovery and the repair stages (Corollaries 7–8, Lemmas 23 and 25).
--
--   **Formalization Note.** The conditional statement is given atom by atom: for every fixed value of the choices of $e$, the average over the remaining choices satisfies the bound.
--
--   Differences from the source:
--   - reading: exp(−Ω(τ_d + τ_dep(a))) → exp(−c·(τ_d + τ_dep(a))) with c > 0 absolute; reason: the asymptotic notation with an explicit absolute constant
--   - encoding: the bound after conditioning on all random choices of the updated edge → for every fixed value of the choices of e, the bound on the average over the outcomes with that value; reason: conditioning on a finite uniform space, atom by atom
--   - encoding: independent uniform directions and categories of the edges at depths d < R → the uniform law on the finite space of choices of every vertex pair at every depth d < R; probabilities and expectations as normalized counts; reason: the choices of non-edges are independent of and irrelevant to the events, so the law of every event is unchanged
--   - reading: "Δ_ε large enough" and Δ > exp(Δ_ε) → an absolute D₀ with the statement for every real E ≥ D₀ and every Δ > exp(E); reason: the existential threshold is the meaning of "large enough"
--   - reading: log in q_d → log base 2; reason: same strength for either base
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Lemma 21, printed p. 35 (PDF p. 37); Definition 8, printed p. 34 (PDF p. 36); proof in §7, printed pp. 39–45 (PDF pp. 41–47)

import Mathlib
import Definitions.Def_DynEdgeColorLLL_Main_Splitting
import Definitions.Def_DynEdgeColorLLL_Main_DynamicSplitting

namespace DynEdgeColorLLL.Main

open Classical in
/-- Lemma 21 (Peng–Ghaffari, STOC 2027 submission #615, printed p. 35, PDF p. 37). Fix an update
`G^old → G^new` (edge `e = {u, v}`) of graphs of maximum degree at most `Δ`, in the regime of
§5.1–§6, with independent uniform directions and categories. For every vertex `w`, every internal
node `a` and every `0 ≤ d < R`,
`E[|{⟨x, b⟩ ∈ K̂(⟨w, a⟩) : dep(b) = d}|] ≤ exp(−Ω(τ_d + τ_{dep(a)}))`; the same bound holds after
conditioning on all random choices of `e`. -/
theorem lemma_21 :
    ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℝ, ∀ E : ℝ, D₀ ≤ E → ∀ Δ : ℕ, Real.exp E < Δ →
      ∀ {V : Type} [Fintype V] [DecidableEq V]
      (Gold Gnew : SimpleGraph V) (u v : V),
      IsEdgeUpdate Gold Gnew u v → (∀ x, Gold.degree x ≤ Δ) → (∀ x, Gnew.degree x ≤ Δ) →
      ∀ (w : V) (a : List Bool) (d : ℕ), a.length < depthR Δ E → d < depthR Δ E →
        randExp Δ E (fun ω : RandSpace V Δ E =>
            (Set.ncard {p | p ∈ hatComponent Δ E Gold Gnew ω.toChoices (w, a) ∧
              p.2.length = d} : ℝ)) ≤
          Real.exp (-(c * (taud Δ d + taud Δ a.length))) ∧
        ∀ ω₀ : RandSpace V Δ E,
          ∑ ω ∈ Finset.univ.filter (fun ω : RandSpace V Δ E => AgreeOnEdge s(u, v) ω₀ ω),
              (Set.ncard {p | p ∈ hatComponent Δ E Gold Gnew ω.toChoices (w, a) ∧
                p.2.length = d} : ℝ) ≤
            Real.exp (-(c * (taud Δ d + taud Δ a.length))) *
              ((Finset.univ.filter fun ω : RandSpace V Δ E =>
                AgreeOnEdge s(u, v) ω₀ ω).card : ℝ) := by sorry

end DynEdgeColorLLL.Main
