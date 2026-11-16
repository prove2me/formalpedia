-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_7_4
-- name    : CompDesign.Supplement.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:01:06.189375+00:00
-- url     : https://prove2.me/theorems/2982a2f4-5861-4043-b6b6-0c614621bf01
-- title:
--   Theorem 7.4 — every randomized cost-oblivious rule loses an $\Omega(\log m)$ factor for $v(S)=|S|$ at some uniform cost
-- statement:
--   Take $B=1$, a single agent with actions $A=\{1,\dots,m\}$, the additive value $v(S)=|S|$ and a uniform cost $c_e=t$; then $\mathrm{OPT}(t)=\max\{|S|:t|S|\le1\}=\min\{m,\lfloor1/t\rfloor\}$. A randomized cost-oblivious rule is a probability distribution $\mu$ over deterministic rules $p:2^A\to[0,1]$; in branch $p$ the agent selects the value $D_p(t)$, the platform-favoring demand.
--
--   **Theorem 7.4 (Logarithmic lower bound for additive values).** There is an absolute constant $C>0$ such that for every $m\ge2$ and every randomized cost-oblivious rule $\mu$ there is a uniform cost $0<t\le1$ with
--   $$\mathbb E_{p\sim\mu}[D_p(t)]\ \le\ \frac{C}{\log m}\,\mathrm{OPT}(t).$$
--
--   So the logarithmic factor of Theorem 7.2 cannot be avoided by any cost-oblivious rule, even for additive values.
--
--   **Formalization Note** $\mu$ is any probability measure on `Finset (Fin m) → ℝ` concentrated on $[0,1]$-valued rules (not only a finite mixture). $D_p(t)$ is a measurable function of $p$ with values in $\{0,\dots,m\}$, so the integral is a genuine expectation.
--
--   Differences from the source:
--   - reading: a randomized cost-oblivious payment rule: a distribution over deterministic rules → any probability measure on Finset (Fin m) → ℝ that is almost surely [0,1]-valued; reason: the most general distribution; finite mixtures are a special case
--   - reading: the expected selected value is at most an O(1/log m) fraction of OPT(t) → ∃ C > 0 such that for all m ≥ 2 and every μ there is t ∈ (0,1] with ∫ D_p(t) dμ ≤ (C/log m)·OPT(t); reason: the O-notation with one absolute constant; m ≥ 2 so that log m > 0
--   - encoding: OPT(t) = min{m, ⌊1/t⌋} → the benchmark (4) for v(S) = |S|, c_e = t, B = 1; reason: the paper's own definition, of which min{m, ⌊1/t⌋} is the value
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 7.4, §7.1.3, p.56 (PDF 59)

import Mathlib
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_Supplement_demand

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 7.4 (Logarithmic lower bound for additive values), §7.1.3, p.56 (PDF 59) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…).
For any randomized cost-oblivious payment rule, there exists a uniform positive cost vector
`c_e = t ≤ 1` such that, for the additive function `v(S) = |S|`, the expected selected value is at
most an `O(1/log m)` fraction of `OPT(t)`.

**Formalization Note.** `B = 1` (p.55). A randomized cost-oblivious rule is any probability measure
`μ` on the deterministic rules `p : 2^A → [0,1]` (`A = Fin m`), not only a finite mixture. In branch
`p` the agent selects value `D_p(t)` (`demand p t`, the platform-favoring cardinality), and the
expected selected value is `∫ D_p(t) dμ(p)`; `D_p(t)` takes values in `{0, …, m}` and is a measurable
function of `p` (it is defined by finitely many comparisons of continuous functions of `p`), so the
integral is a genuine expectation. `OPT(t)` is the benchmark (4) for `v(S) = |S|`, uniform cost `t`
and `B = 1`, i.e. `min{m, ⌊1/t⌋}`. `O(1/log m)` is read with one absolute constant `C > 0` for all
`m ≥ 2`. -/
theorem theorem_7_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ μ : MeasureTheory.Measure (Finset (Fin m) → ℝ),
      MeasureTheory.IsProbabilityMeasure μ → (∀ᵐ p ∂μ, ∀ S, 0 ≤ p S ∧ p S ≤ 1) →
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        ∫ p, (demand p t : ℝ) ∂μ ≤
          C / Real.log m * OPT (fun S : Finset (Fin m) => (S.card : ℝ)) 1 (fun _ => t) := by sorry

end CompDesign.Supplement
