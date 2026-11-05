-- Prove2me | Theorems.Thm_CalendarDependentRM_lemma_J_3
-- name    : CalendarDependentRM.lemma_J_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:25.749708+00:00
-- url     : https://prove2.me/theorems/e355c449-d4fb-4121-8193-dfad63896168
-- title:
--   Lemma J.3: the Doob martingale has bounded increments
-- statement:
--   Assume the transition assumption with $\epsilon>0$, and let $x$ be feasible for the fluid approximation. For all $i$ and all stages $\ell+1\le m$, with probability one,
--
--   $$
--   |M^m_i(\ell)-M^m_i(\ell+1)|\le\frac2{\epsilon^3},
--   $$
--
--   where $M^m_i(\ell)=E\{V^m_i\mid D^\ell,\dots,D^m\}$. Azuma's method then applies to the expected consumption along the demand path.
--
--   Differences from the source:
--   - generalization: $x$ an optimal solution of problem (2) → any feasible $x$; reason: the argument uses only the constraints of (2); an optimal solution is feasible
--   - reading: $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ for all $p,q\in\mathcal T$, $k\in\mathcal K$ → the bound holds for the transitions between stages of the horizon, into stages $2,\dots,K$, with no condition on $D^1$ given $\hat D^0$; reason: at $k=K$ the printed condition names a nonexistent $D^{K+1}$; this literal reading is the weakest hypothesis, so the result covers every other reading
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
--   - generalization: the draws $A^k_{jt}$, $X^k_{jt}(q)$ are independent Bernoulli variables, independent of the demands → `PolicyRun` lets the $X^k_{jt}(q)$ of different $(j,q)$ in one period be correlated; reason: the statement involves the run only through its demands and the deterministic $n^k_{it}(q)$; every fully independent family is a run
--   - encoding: conditional probabilities given a null event are undefined → they read $0$ (a ratio with $0/0=0$), or the zero measure for `cond`; reason: $M^k_i(\ell)$ is evaluated on the atom of $D^{[\ell,k]}$ through `cond`; the atoms of mass $0$ form a null set, outside the almost-sure statement
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, Lemma J.3, ER p.22 (PDF 44)

import Mathlib
import Definitions.Def_CalendarDependentRM_PolicyRun

open MeasureTheory ProbabilityTheory

namespace CalendarDependentRM

/-- **Lemma J.3.** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Lemma J.3, Extended Results p. 22 (PDF p. 44):
for all `i` and `k`, `ℓ` with `ℓ + 1 ≤ k`, with probability one, `|M^k_i(ℓ) − M^k_i(ℓ + 1)| ≤ 2/ε³`.

**Formalization Note** `m` (the paper's `k`) and `ℓ` are the paper's stage numbers: `1 ≤ ℓ`, `ℓ + 1 ≤ m ≤ K`. The paper's
proof uses `T ≤ 1/ε`; it follows from `Minorized` here, since `m ≥ 2` gives a transition between stages. `x` is feasible;
the paper's is optimal. -/
theorem lemma_J_3 {R J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {K T : ℕ} {I : Instance R J K T} {ε : ℝ} (hε : 0 < ε) (hmin : I.chain.Minorized ε) {γ : ℝ}
    {x : Fin K → J → Fin T → Fin T → ℝ} (hx : I.Feasible x)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (run : PolicyRun I γ x P) (i : R) (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hm : ℓ + 1 ≤ m) (hmK : m ≤ K) :
    ∀ᵐ ω ∂P, |run.M i m ℓ ω - run.M i m (ℓ + 1) ω| ≤ 2 / ε ^ 3 := by sorry

end CalendarDependentRM
