-- Prove2me | Theorems.Thm_EthierKurtz_hille_yosida_closed_dissipative_relation
-- name    : EthierKurtz.hille_yosida_closed_dissipative_relation
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-25T05:13:29.871582+00:00
-- url     : https://prove2.me/theorems/ada2c5f9-e64a-4d8a-ad77-a0467044074b
-- title:
--   Hille-Yosida for a closed dissipative linear relation with dense domain and dense range
-- statement:
--   Let $E$ be a real Banach space and let $A \subseteq E \times E$ be a closed linear relation (a possibly multivalued linear operator). Suppose $A$ is dissipative,
--   $$\lambda\|f\| \le \|\lambda f - g\| \quad ((f,g) \in A,\ \lambda > 0),$$
--   the range of $\lambda_0 - A$ is dense for some $\lambda_0 > 0$, and the domain $\{f : (f,g) \in A\}$ is dense in $E$. Then there is a strongly continuous contraction semigroup $T$ on $E$ whose generator is exactly $A$:
--   $$\lim_{t \downarrow 0} t^{-1}(T_t f - f) = g \iff (f,g) \in A.$$
--
--   Role: this is the abstract Banach-space Hille-Yosida generation theorem that the parent applies to the closure of the reflected diffusion graph on $C(\bar\Omega)$; the parent supplies dissipativity and dense range as hypotheses, and density of the domain comes from a separate child.
--
--   **Formalization Note**: $A$ is a `Submodule` of `E × E`; the semigroup is indexed by all reals but only $t \ge 0$ matters, as in `IsStronglyContinuousContractionSemigroup`.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658. Chapter 1, Section 2, Theorem 2.6 (Hille-Yosida), with Chapter 1, Section 4 (multivalued linear operators)

import Mathlib
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology

namespace EthierKurtz

theorem hille_yosida_closed_dissipative_relation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (A : Submodule ℝ (E × E)) (hclosed : IsClosed (A : Set (E × E)))
    (hdiss : ∀ fg ∈ A, ∀ lam : ℝ, 0 < lam → lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖)
    (hrange : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : E, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ A, ‖(lam₀ • fg.1 - fg.2) - h‖ < delta)
    (hdense : ∀ h : E, ∀ delta : ℝ, 0 < delta → ∃ fg ∈ A, ‖fg.1 - h‖ < delta) :
    ∃ T : ℝ → E →L[ℝ] E,
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) := by sorry

end EthierKurtz
