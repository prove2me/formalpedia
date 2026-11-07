-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_lemma_3_2
-- name    : ArgmaxDeFinetti.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:35.823487+00:00
-- url     : https://prove2.me/theorems/dba03eb6-69c3-4aa3-9ec9-4ce946d73368
-- title:
--   Lemma 3.2 — exact trace-norm duality
-- statement:
--   For every $N,d\ge2$,
--   $$
--   D^{\mathrm{tr}}_H\big(\mathrm{BOS}^{(2)}_N(d),\mathrm{SEP}^{(2)}_H(d)\big)=\frac12\sup_{\substack{M\in\mathrm{Herm}(\mathrm{Sym}^2\mathcal H)\\ \|M\|_\infty\le1}}\Big\{\lambda_{\max}(M^{[N]})-h(M)\Big\},
--   $$
--   where $\mathcal H=\mathbb C^d$, $\mathrm{BOS}^{(2)}_N(d)$ is the set of two-site marginals of bosonic $N$-site states, $\mathrm{SEP}^{(2)}_H(d)$ the Hartree mixtures, $D^{\mathrm{tr}}_H$ the Hausdorff distance for the normalized trace distance, $M^{[N]}$ the normalized $N$-site lift (3.4), $\lambda_{\max}$ its top eigenvalue on $\mathrm{Sym}^N$, and $h(M)=\max_{\|u\|=1}\langle u^{\otimes2}|M|u^{\otimes2}\rangle$.
--
--   The de Finetti error is thus exactly half the largest integrality gap between the bosonic and Hartree values of a bounded witness.
--
--   Differences from the source:
--   - encoding: N ≥ 2 → N = 2 + m with m : ℕ; reason: the same values of N
--   - encoding: M ∈ Herm(Sym²(H)) → a Hermitian matrix on ℂ^d ⊗ ℂ^d with U_π M = M U_π = M for π ∈ S₂ (IsSymWitness); reason: extension by zero of the operator on Sym²; it has the same operator norm, a_M, h(M), lift and τ(M)
--   - encoding: λ_max(M^[N]) of M^[N] on Sym^N(H) → supremum of Re⟨ψ, M^[N]ψ⟩ over unit ψ ∈ Sym^N (lamMaxSym); reason: the top eigenvalue of a Hermitian operator on Sym^N is its largest Rayleigh quotient
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Lemma 3.2, p.23, eq. (3.5)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_opNormS
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ArgmaxDeFinetti_hausdorff
import Definitions.Def_ArgmaxDeFinetti_hartree2
import Definitions.Def_ArgmaxDeFinetti_bos2
import Definitions.Def_ArgmaxDeFinetti_IsSymWitness
import Definitions.Def_ArgmaxDeFinetti_hM
import Definitions.Def_ArgmaxDeFinetti_lamMaxSym

open Matrix
open scoped ComplexOrder

namespace ArgmaxDeFinetti

/-- **Lemma 3.2 (Exact trace-norm duality)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.23, eq. (3.5). For every `N, d ≥ 2`,
`D^tr_H(BOS^{(2)}_N(d), SEP^{(2)}_H(d)) = ½ sup_{M ∈ Herm(Sym² H), ∥M∥_∞ ≤ 1} {λ_max(M^{[N]}) − h(M)}`.

**Formalization Note** `N = 2 + m`. The left side is the Hausdorff distance (2.6) with the trace distance (2.1);
`M ∈ Herm(Sym²H)` is `IsSymWitness M`, `∥M∥_∞` is `opNormS`, `λ_max(M^{[N]})` is the top eigenvalue on `Sym^N`
(`lamMaxSym`), `h(M)` is (3.3). The supremum is a real `sSup`, as printed. -/
theorem lemma_3_2 (m d : ℕ) (hd : 2 ≤ d) :
    hausdorff DimFreeShadow.traceDistance (bos2 m d) (hartree2 d) =
      (1 / 2 : ℝ) * sSup {r | ∃ M : Op 2 d, IsSymWitness M ∧ opNormS M ≤ 1 ∧
        r = lamMaxSym (2 + m) M - hM M} := by sorry

end ArgmaxDeFinetti
