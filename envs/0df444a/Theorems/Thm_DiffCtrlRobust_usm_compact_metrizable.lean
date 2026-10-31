-- Prove2me | Theorems.Thm_DiffCtrlRobust_usm_compact_metrizable
-- name    : DiffCtrlRobust.usm_compact_metrizable
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:29.608077+00:00
-- url     : https://prove2.me/theorems/20579d7f-7679-4ccf-9e74-615bdd37eaab
-- title:
--   §2, p.6 — $\mathfrak U_{\mathsf{sm}}$ is compact metrizable
-- statement:
--   There is a compact pseudometric on $\mathfrak U_{\mathsf{sm}}$ such that for all sequences $v_n$ and all $v$,
--
--   $$
--   \mathrm{dist}(v_n,v)\to0\quad\Longleftrightarrow\quad v_n\to v\text{ in the topology of p.6,}
--   $$
--
--   that is, $\int f\int g\,\mathrm dv_n\,\mathrm dx\to\int f\int g\,\mathrm dv\,\mathrm dx$ for all $f\in L^1\cap L^2$ and $g\in\mathcal C_b(\mathbb R^d\times\mathbb U)$.
--
--   Compactness of the space of Markov policies is what produces a limit policy from a sequence of optimal policies.
--
--   Differences from the source:
--
--   - encoding: U a compact metric space, min over U → U also nonempty; reason: a minimum over U presupposes it
--   - encoding: 𝔘sm is metrizable with compact metric → a compact pseudometric on the Borel maps; reason: controls equal a.e. are not separated by the test functions; two controls at distance 0 agree a.e., so the metric of the paper lives on the quotient
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2, p.6, citing [9, Section 2.4, Lemma 2.4.1]

import Definitions.Def_DiffCtrlRobust_UsmTendsto

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- `𝔘sm` is compact metrizable (arXiv:2205.05894v2, §2, p.6, citing Arapostathis–Borkar–Ghosh,
§2.4 and Lemma 2.4.1): there is a compact pseudometric on `𝔘sm` whose convergent sequences are
exactly those of `UsmTendsto`.

**Formalization Note.** A pseudometric, because controls that agree a.e. have the same convergent
sequences; two controls at distance `0` agree a.e., and the metric of the paper lives on the
quotient. -/
theorem usm_compact_metrizable {d : ℕ} {U : Type*} [MetricSpace U] [CompactSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U] :
    ∃ m : PseudoMetricSpace (Usm d U),
      (∀ (vs : ℕ → Usm d U) (v : Usm d U),
        Tendsto (fun n => m.dist (vs n) v) atTop (𝓝 0) ↔ UsmTendsto vs v) ∧
      @CompactSpace (Usm d U) m.toUniformSpace.toTopologicalSpace := by sorry

end DiffCtrlRobust
