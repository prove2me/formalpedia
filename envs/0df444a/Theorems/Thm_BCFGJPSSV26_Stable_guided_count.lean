-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_guided_count
-- name    : BCFGJPSSV26.Stable.guided_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:45:39.818703+00:00
-- url     : https://prove2.me/theorems/1639f517-02e9-42a8-9b0d-632ec805b510
-- title:
--   Guided counting — an invariant kept by a fraction $q$ of the inputs at each step survives $M$ steps with fraction $q^M$
-- statement:
--   A counting lemma for step-by-step randomized processes, not specific to the paper: if from every state satisfying an invariant at least a fraction $q$ of the next inputs keeps it, then at least a fraction $q^M$ of the input sequences of length $M$ keeps it for $M$ steps.
--
--   **Setting.** Let $\sigma$ be a set of states and $\chi$ a finite set of inputs. Let $\mathrm{step}_t:\sigma\times\chi\to\sigma$ be a transition function for each time $t\in\mathbb N$, and $x_0\in\sigma$ an initial state. For $u=(u_0,\dots,u_{M-1})\in\chi^M$ let $x_0(u)=x_0$ and $x_{t+1}(u)=\mathrm{step}_t(x_t(u),u_t)$. Let $\mathrm{Inv}_t$ be a property of states and $G_t$ a relation between states and inputs ("$u$ is a good input for $x$ at time $t$"), for each $t$. Let $q\ge0$ be a real number and $M$ a natural number.
--
--   **Statement.** Assume that
--
--   1. $\mathrm{Inv}_0(x_0)$ holds;
--   2. for all $t\lt M$, all states $x$ and inputs $u$: if $\mathrm{Inv}_t(x)$ and $G_t(x,u)$ then $\mathrm{Inv}_{t+1}(\mathrm{step}_t(x,u))$;
--   3. for all $t\lt M$ and all states $x$ with $\mathrm{Inv}_t(x)$: $\#\{u\in\chi:\ G_t(x,u)\}\ge q\,|\chi|$.
--
--   Then
--   $$\#\bigl\{u\in\chi^M:\ \mathrm{Inv}_M\bigl(x_M(u)\bigr)\bigr\}\ \ge\ q^M\,|\chi|^M .$$
--
--   The lemma is what turns the analyses of the client sampling and of the cluster sampling of Part II (Algorithms 1 and 2) into lower bounds on success probabilities: the states are those of the sampling, the inputs are chunks of coins (or triples of chunks), and the invariant at the end is a good outcome in the sense of the sampling theorems of Part II, Sections 4.2 and 4.4.
--
--   **Formalization Note** The good inputs may depend on the state in an arbitrary way, so no independence is used: the inputs are counted, not weighted by a probability measure.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.Stable.guided_count`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/Coins.lean#L335-L375

module

public import Definitions.Def_BCFGJPSSV26_Model
public import Definitions.Def_BuhaiPapers_Background_Sampling
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Fin.Basic
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset Sampling

open Classical in

theorem guided_count {σ χ : Type*} [Fintype χ] (step : ℕ → σ → χ → σ) (x₀ : σ)
    (Inv : ℕ → σ → Prop) (G : ℕ → σ → χ → Prop) {q : ℝ} (hq : 0 ≤ q) (M : ℕ) (h0 : Inv 0 x₀)
    (hstep : ∀ t < M, ∀ x u, Inv t x → G t x u → Inv (t + 1) (step t x u))
    (hG : ∀ t < M, ∀ x, Inv t x → q * Fintype.card χ ≤ (univ.filter fun u ↦ G t x u).card) :
    q ^ M * (Fintype.card χ : ℝ) ^ M ≤
      (univ.filter fun u : Fin M → χ ↦ Inv M (runFin step x₀ M u)).card := by sorry

end BCFGJPSSV26.Stable
end
