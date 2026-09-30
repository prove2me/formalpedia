-- Prove2me | Theorems.Thm_Avram2004_Russian_lemma1_ratio_limit
-- name    : Avram2004.Russian.lemma1_ratio_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:06:15.979677+00:00
-- url     : https://prove2.me/theorems/b637690e-9d3f-4dd5-b602-bf62961692bb
-- title:
--   Lemma 1 — Z^(q)(x)/W^(q)(x) → q/Φ(q) as x → ∞, for q ≥ 0
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumption, with Laplace exponent $\psi$, and let $\Phi(q)$ be the largest root of $\psi(\theta)=q$. For every $q\ge0$,
--   $$\lim_{x\to\infty}\frac{Z^{(q)}(x)}{W^{(q)}(x)}=\frac{q}{\Phi(q)} ,$$
--   where for $q=0$ the quotient $0/\Phi(0)$ is understood, as in the paper, to mean $\lim_{\theta\downarrow0}\theta/\Phi(\theta)$ $(=0\vee\psi'(0))$.
--
--   The ratio $Z^{(q)}/W^{(q)}$ controls the sign of $f=Z^{(q)}-qW^{(q)}$ at infinity, which is how Lemma 2 locates the optimal level $\kappa^*$.
--
--   **Formalization Note** The paper states the lemma for $q\ge0$, with the convention that $0/\Phi(0)$ means $\lim_{\theta\downarrow0}\theta/\Phi(\theta)=0\vee\psi'(0)$. The statement asserts a real limit $L$ of the ratio, with $L=q/\Phi(q)$ when $q>0$ (then $\Phi(q)>0$) and, when $q=0$, $L$ equal to the limit of $\theta/\Phi(\theta)$ as $\theta\downarrow0$ (for $\theta>0$, $\Phi(\theta)>0$). The convention is written out explicitly, never as Lean's $0/0=0$. For $x>0$, $W^{(q)}(x)>0$, so the ratio has no junk value near infinity.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 218, Lemma 1 (and the convention for 0/Φ(0) stated before it)

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Avram2004.Russian

/-- Lemma 1, p. 218: for `q ≥ 0`, `lim_{x→∞} Z^{(q)}(x) / W^{(q)}(x) = q / Φ(q)`, where for `q = 0` the
quotient `0/Φ(0)` means, as the paper stipulates, `lim_{θ↓0} θ/Φ(θ)` (`= 0 ∨ ψ′(0)`): the limit `L`
of the ratio equals `q / Φ(q)` when `q > 0`, and for `q = 0` it is the limit of `θ / Φ(θ)` as `θ ↓ 0`. -/
theorem lemma1_ratio_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevy P X) (hS : Shared.Standing P X) (q : ℝ) (hq : 0 ≤ q) :
    ∃ L : ℝ, (0 < q → L = q / Shared.Phi (Shared.psi P X) q) ∧
      (q = 0 → Tendsto (fun θ => θ / Shared.Phi (Shared.psi P X) θ) (𝓝[>] 0) (𝓝 L)) ∧
      Tendsto (fun x => Shared.Z P X 0 q x / Shared.W P X 0 q x) atTop (𝓝 L) := by sorry

end Avram2004.Russian
