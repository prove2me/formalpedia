-- Prove2me | Theorems.Thm_DistQuantumQuery_lemma_7_9
-- name    : DistQuantumQuery.lemma_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:54.535199+00:00
-- url     : https://prove2.me/theorems/976d78c9-7a29-4127-b6d7-569267f03e9f
-- title:
--   Lemma 7.9 — $\mathrm{rAdv}^{(1/2,1/2)}_\varepsilon(\mathrm{TRIV})=1-\varepsilon$
-- statement:
--   Let $\mathrm{TRIV}:\{0^n,1^n\}\to\{0,1\}$, $\mathrm{TRIV}(b^n)=b$, with $n\ge1$, and let $(1/2,1/2)$ be the uniform distribution on $\{0^n,1^n\}$. For $\varepsilon\in[0,1]$,
--   $$
--   \mathrm{rAdv}^{(1/2,1/2)}_\varepsilon(\mathrm{TRIV})=1-\varepsilon .
--   $$
--   This exact value is the normalization in the TRIV characterization of $\mathrm{sfAdv}$ (Proposition 7.10).
--
--   **Formalization Note** The $n\ge1$ positions form a nonempty finite type.
--
--   Differences from the source:
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: TRIV on {0^n, 1^n} with positions [n], n ≥ 1 → positions a nonempty finite type ι; TRIV(x) = [x = 1^n]; reason: relabelling positions; [x = 1^n] is b on b^n when ι is nonempty
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Lemma 7.9, p.63; §7.1.5, p.63

import Mathlib
import Definitions.Def_DistQuantumQuery_rAdv
import Definitions.Def_DistQuantumQuery_compose

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Lemma 7.9** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Lemma 7.9, p.63). For `ε ∈ [0,1]`, `rAdv^{(1/2,1/2)}_ε(TRIV) = 1 − ε`.

**Formalization Note** `TRIV : {0^n, 1^n} → {0,1}` on `n ≥ 1` positions (a nonempty finite type
`ι`); `(1/2, 1/2)` is the uniform distribution on `{0^n, 1^n}`; the filters are the `n` query
filters of `{0^n, 1^n}`. -/
theorem lemma_7_9 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    rAdv (trivSet ι) (fun _ => 1 / 2) triv ε = ENNReal.ofReal (1 - ε) := by sorry

end DistQuantumQuery
