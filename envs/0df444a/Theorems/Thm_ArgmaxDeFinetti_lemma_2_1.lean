-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_lemma_2_1
-- name    : ArgmaxDeFinetti.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:38.376204+00:00
-- url     : https://prove2.me/theorems/a8e8607f-8306-4722-bdb2-972255d4305c
-- title:
--   Lemma 2.1 — distance duality for compact convex state sets
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space and $L\subseteq D(\mathcal H)$ a nonempty, compact, convex set of states. For every state $\rho\in D(\mathcal H)$,
--   $$
--   D_{\mathrm{tr}}(\rho,L)=\max_{0\preceq M\preceq I}\{\operatorname{Tr}(M\rho)-h_L(M)\}=\tfrac12\max_{\substack{M\in\mathrm{Herm}(\mathcal H)\\ \|M\|_\infty\le1}}\{\operatorname{Tr}(M\rho)-h_L(M)\},
--   $$
--   $$
--   D_{\mathrm{HS}}(\rho,L)=\max_{\substack{M\in\mathrm{Herm}(\mathcal H)\\ \|M\|_2\le1}}\{\operatorname{Tr}(M\rho)-h_L(M)\}=\max_{\substack{M\in\mathrm{Herm}(\mathcal H)\\ \operatorname{Tr}M=0,\ \|M\|_2\le1}}\{\operatorname{Tr}(M\rho)-h_L(M)\}.
--   $$
--   If $K\subseteq D(\mathcal H)$ is also nonempty, compact and convex, and $L\subseteq K$, then
--   $$
--   D^{\mathrm{tr}}_H(K,L)=\max_{0\preceq M\preceq I}\{h_K(M)-h_L(M)\}=\tfrac12\max_{\substack{M\in\mathrm{Herm}(\mathcal H)\\ \|M\|_\infty\le1}}\{h_K(M)-h_L(M)\},
--   $$
--   $$
--   D^{\mathrm{HS}}_H(K,L)=\max_{\substack{M\in\mathrm{Herm}(\mathcal H)\\ \operatorname{Tr}M=0,\ \|M\|_2\le1}}\{h_K(M)-h_L(M)\}.
--   $$
--   Here $D_{\mathrm{tr}}=\tfrac12\|\cdot\|_1$, $D_{\mathrm{HS}}=\|\cdot\|_2$, $D^\star(\rho,L)$ is the distance to a set, $D^\star_H$ the Hausdorff distance and $h_C$ the support function. Every maximum is attained.
--
--   The identity for $D^{\mathrm{tr}}_H$ is what turns the de Finetti error into a gap of support functions (Lemma 3.2).
--
--   Differences from the source:
--   - encoding: H a finite-dimensional complex Hilbert space, D(H) its density operators → ℂ^ι for a finite type ι, density operators WildeQIT.IsDensityOperator (PSD, trace one); reason: every such H is ℂ^ι in an orthonormal basis
--   - encoding: value = max S, and value = ½ max S → IsGreatest S value, and IsGreatest S (2 · value); reason: the same claims, including that the maximum is attained
--   - encoding: 0 ⪯ M ⪯ I → M ⪰ 0 and I − M ⪰ 0; reason: the same set of operators
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Lemma 2.1, pp.20–21, eqs. (2.9)–(2.12)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ArgmaxDeFinetti_opNormS
import Definitions.Def_WildeQIT_hsNorm
import Definitions.Def_ArgmaxDeFinetti_hsDist
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ArgmaxDeFinetti_hausdorff
import Definitions.Def_ArgmaxDeFinetti_supportFn

open Matrix
open scoped ComplexOrder

namespace ArgmaxDeFinetti

/-- **Lemma 2.1 (Distance duality for compact convex state sets)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), pp.20–21, eqs. (2.9)–(2.12).

Let `L ⊆ D(H)` be nonempty, compact and convex. For every state `ρ`,
`D_tr(ρ, L) = max_{0⪯M⪯I} {Tr(Mρ) − h_L(M)} = ½ max_{M Hermitian, ∥M∥_∞≤1} {Tr(Mρ) − h_L(M)}` (2.9) and
`D_HS(ρ, L) = max_{M Hermitian, ∥M∥₂≤1} {…} = max_{M Hermitian, Tr M = 0, ∥M∥₂≤1} {…}` (2.10). If also `K ⊆ D(H)`
is nonempty, compact, convex and `L ⊆ K`, then
`D^tr_H(K, L) = max_{0⪯M⪯I} {h_K(M) − h_L(M)} = ½ max_{M Hermitian, ∥M∥_∞≤1} {h_K(M) − h_L(M)}` (2.11) and
`D^HS_H(K, L) = max_{M Hermitian, Tr M = 0, ∥M∥₂≤1} {h_K(M) − h_L(M)}` (2.12).

**Formalization Note** `H = ℂ^ι`; states are `WildeQIT.IsDensityOperator`. Each "`= max S`" is
`IsGreatest S value` (attained maximum), and "`= ½ max S`" is `IsGreatest S (2 · value)`. `0 ⪯ M ⪯ I` is
`M ⪰ 0 ∧ I − M ⪰ 0` (which makes `M` Hermitian). `D^⋆_H` is the Hausdorff distance (2.6) (`hausdorff`), `D_tr` is the published `DimFreeShadow.traceDistance` (`½ ∥·∥₁`), `∥·∥₂` the published
`WildeQIT.hsNorm`,
`D^⋆(ρ, L)` the set distance (2.5) (`distSet`), `h` the support function (2.8). -/
theorem lemma_2_1 {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : Set (Matrix ι ι ℂ)) (hLne : L.Nonempty) (hLc : IsCompact L) (hLcv : Convex ℝ L)
    (hLD : ∀ σ ∈ L, WildeQIT.IsDensityOperator σ) :
    (∀ ρ : Matrix ι ι ℂ, WildeQIT.IsDensityOperator ρ →
      IsGreatest {r | ∃ M : Matrix ι ι ℂ, M.PosSemidef ∧ (1 - M).PosSemidef ∧
          r = (Matrix.trace (M * ρ)).re - supportFn L M} (distSet DimFreeShadow.traceDistance ρ L) ∧
      IsGreatest {r | ∃ M : Matrix ι ι ℂ, M.IsHermitian ∧ opNormS M ≤ 1 ∧
          r = (Matrix.trace (M * ρ)).re - supportFn L M} (2 * distSet DimFreeShadow.traceDistance ρ L) ∧
      IsGreatest {r | ∃ M : Matrix ι ι ℂ, M.IsHermitian ∧ WildeQIT.hsNorm M ≤ 1 ∧
          r = (Matrix.trace (M * ρ)).re - supportFn L M} (distSet hsDist ρ L) ∧
      IsGreatest {r | ∃ M : Matrix ι ι ℂ, M.IsHermitian ∧ M.trace = 0 ∧ WildeQIT.hsNorm M ≤ 1 ∧
          r = (Matrix.trace (M * ρ)).re - supportFn L M} (distSet hsDist ρ L)) ∧
    (∀ K : Set (Matrix ι ι ℂ), K.Nonempty → IsCompact K → Convex ℝ K →
      (∀ σ ∈ K, WildeQIT.IsDensityOperator σ) → L ⊆ K →
      IsGreatest {r | ∃ M : Matrix ι ι ℂ, M.PosSemidef ∧ (1 - M).PosSemidef ∧
          r = supportFn K M - supportFn L M} (hausdorff DimFreeShadow.traceDistance K L) ∧
      IsGreatest {r | ∃ M : Matrix ι ι ℂ, M.IsHermitian ∧ opNormS M ≤ 1 ∧
          r = supportFn K M - supportFn L M} (2 * hausdorff DimFreeShadow.traceDistance K L) ∧
      IsGreatest {r | ∃ M : Matrix ι ι ℂ, M.IsHermitian ∧ M.trace = 0 ∧ WildeQIT.hsNorm M ≤ 1 ∧
          r = supportFn K M - supportFn L M} (hausdorff hsDist K L)) := by sorry

end ArgmaxDeFinetti
