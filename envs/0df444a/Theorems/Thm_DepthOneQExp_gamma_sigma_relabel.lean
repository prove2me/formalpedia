-- Prove2me | Theorems.Thm_DepthOneQExp_gamma_sigma_relabel
-- name    : DepthOneQExp.gamma_sigma_relabel
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:52:21.126963+00:00
-- url     : https://prove2.me/theorems/869c30d0-9f72-4e41-8d83-4d964a14688a
-- title:
--   Proof of Theorem 2.3, Eqs. (2.23)–(2.25): after relabelling the qubits, $\Gamma(\Sigma_{3s}) = \{U_3,\dots,U_{16}\}$
-- statement:
--   For every $s\ge1$, each generator in $\Gamma(\Sigma_{3s})$ is a product of CNOT gates on non-overlapping qubits (Eqs. (2.23)–(2.25)), and after the qubits are re-indexed by $1,4,\dots,3s-2,\ 2,5,\dots,3s-1,\ 3,6,\dots,3s$, these 14 circuits are exactly $U_3,\dots,U_{16}$ of Theorem 2.2: there is a bijection $\tau$ of the 14 indices such that, for every $j$,
--   $$
--   R\,\Gamma(\sigma_j)\,R^{-1} = U_{\tau(j)+3},
--   $$
--   where $R$ is the induced relabelling of the computational basis.
--
--   This identification is what lets Theorem 2.3 transfer the spectral bounds for $\mathrm{SL}(3s;\mathbb F_2)$ to the circuits $U_3,\dots,U_{16}$.
--
--   **Formalization Note** Equality as permutations of the computational basis (equivalently, of their permutation matrices).
--
--   Differences from the source:
--   - encoding: "these circuits become exactly U_3, …, U_16" → ∃ a bijection τ of Fin 14 with relabel · Γ(σ_j) · relabel⁻¹ = U_{τ(j)+3} for all j; reason: the paper does not fix which generator becomes which U_i; equality of the two 14-element families up to order
--   - encoding: qubits labelled 1, …, n → qubits labelled 0, …, n − 1 (paper qubit p is index (p − 1) mod n); reason: Lean indexing convention; same gates
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), proof of Theorem 2.3, Eqs. (2.23)–(2.25) and the following sentence, p.11

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_gamma
import Definitions.Def_DepthOneQExp_sigma
import Definitions.Def_DepthOneQExp_relabel
import Definitions.Def_DepthOneQExp_cnotGroup
import Definitions.Def_DepthOneQExp_cnotU

namespace DepthOneQExp

/-- Proof of Theorem 2.3, Eqs. (2.23)–(2.25) and the sentence after them
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, p.11): for every `s ≥ 1`,
after relabelling the `3s` qubits by `1, 4, …, 3s − 2, 2, 5, …, 3s − 1, 3, 6, …, 3s`, the 14
circuits `Γ(g)`, `g ∈ Σ_{3s}`, become exactly `U_3, …, U_16`: there is a bijection `τ` of the 14
indices with `relabel ∘ Γ(σ_j) ∘ relabel⁻¹ = U_{τ(j)+3}` for every `j`.

**Formalization Note** Equality as permutations of the computational basis (equivalently, of their
permutation matrices). `relabel s` sends the qubit in old position `a·s + i` to new position `3i + a`
(0-based). -/
theorem gamma_sigma_relabel (s : ℕ) (hs : 1 ≤ s) :
    ∃ τ : Fin 14 ≃ Fin 14, ∀ j : Fin 14,
      relabel s * gamma (3 * s) (sigma s j) * (relabel s)⁻¹ =
        ((cnotU s (τ j) : cnotGroup (3 * s)) : Equiv.Perm (MITMSynthesis.Q (3 * s))) := by sorry

end DepthOneQExp
