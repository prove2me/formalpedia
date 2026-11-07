-- Prove2me | Theorems.Thm_EuclidSPAgg_theorem_4_1
-- name    : EuclidSPAgg.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:46.374199+00:00
-- url     : https://prove2.me/theorems/8d0efc05-f29f-4add-afdb-f8779ead5114
-- title:
--   Theorem 4.1 — a core of a symmetric strategyproof ternary rule is an orthogonal box, on which the rule is the coordinate-wise median
-- statement:
--   Let $H:E^3\to E$ be symmetric, continuous and strategyproof in each argument, and let $C$ be a core of $H$. Then $C$ is an orthogonal box, and in a corresponding orthonormal frame $\mathcal B$,
--   $$
--   H(a,b,c)=\mathrm{CM}_{\mathcal B}(a,b,c)\qquad(a,b,c\in C),
--   $$
--   where $\mathrm{CM}_{\mathcal B}$ of three points selects, in each coordinate of $\mathcal B$, the median of the three coordinates.
--
--   This is the geometric heart of the characterization: it determines both the shape of every core and the operation the rule induces on it.
--
--   **Formalization Note** Both conclusions use one orthonormal basis $\mathcal B$ of $E$: $C$ is the set of points whose $\mathcal B$-coordinates lie in nonempty closed intervals $J_j$, and on $C^3$ the rule is the order-statistic rule of rank 2 (the 0-based index 1) in $\mathcal B$.
--
--   Differences from the source:
--   - reading: an orthonormal affine frame B of aff C → an orthonormal basis of E in which the factors normal to aff C are singletons; reason: the paper's convention that an intrinsic frame extends to the ambient space by singleton factors (p.9); on C³ the median in the extended frame equals the median in the intrinsic frame
--   - encoding: H symmetric; CM_B(a, b, c) → IsAnonymous H; Q B with every rank index 1 : Fin 3; reason: a symmetric ternary rule is an anonymous 3-agent mechanism, and the median of three is rank 2
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem 4.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_IsAnonymous
import Definitions.Def_EuclidSPAgg_Q
import Definitions.Def_EuclidSPAgg_IsCore
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Theorem 4.1** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.14 (PDF p.16)). Let `H : E³ → E` be symmetric, continuous and
strategyproof in each argument, and let `C` be a core of `H`. Then `C` is an orthogonal box. In a
corresponding orthonormal affine frame `B` of `aff C`, `H(a, b, c) = CM_B(a, b, c)` for all
`a, b, c ∈ C`.

**Formalization Note** "Symmetric" is anonymity of the 3-agent rule. Both conclusions are stated
in one frame: an orthonormal basis `B` of `E` and closed nonempty interval factors `J j` with
`C = {x | ∀ j, ⟨B j, x⟩ ∈ J j}`; the intrinsic frame of `aff C` is extended to `E` by singleton
factors, the paper's convention (p.9), and on `C³` the coordinate-wise median in the extended frame
agrees with the one in the intrinsic frame. `CM_B` of three reports is `Q B k` with every rank 2,
the 0-based index `1 : Fin 3`. `d ≥ 1` is standing (p.8). -/
theorem theorem_4_1 {d : ℕ} (hd : 1 ≤ d) (H : Mech 3 d) (hA : IsAnonymous H)
    (hC : Continuous H) (hSP : IsStrategyproof H) (C : Set (E d)) (hcore : IsCore H C) :
    ∃ (B : OrthonormalBasis (Fin d) ℝ (E d)) (J : Fin d → Set ℝ),
      (∀ j, (J j).Nonempty ∧ IsClosed (J j) ∧ (J j).OrdConnected) ∧
      C = {x | ∀ j, inner ℝ (B j) x ∈ J j} ∧
      ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, H ![a, b, c] = Q B (fun _ => (1 : Fin 3)) ![a, b, c] := by sorry

end EuclidSPAgg
