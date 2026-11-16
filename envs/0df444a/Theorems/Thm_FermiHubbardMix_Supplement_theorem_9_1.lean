-- Prove2me | Theorems.Thm_FermiHubbardMix_Supplement_theorem_9_1
-- name    : FermiHubbardMix.Supplement.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:07:28.881202+00:00
-- url     : https://prove2.me/theorems/ab89b16e-25d3-4305-9ef1-a6fe476abb47
-- title:
--   Theorem 9.1 — separability of $e^{-\beta H}/\mathrm{tr}\,e^{-\beta H}$ for $h\le\frac1{8\beta L}\log\frac1{4DL\beta}$
-- statement:
--   Let $H=V+W$ act on $n$ qubits, where $W$ is a bounded $L$-local degree-$D$ Hamiltonian and $V=\sum_iV_i$ is an external field with $V_i$ supported on site $i$ only. Let $h=\max_i\|V_i\|$ (operator norm). If
--   $$
--   0<\beta\le\frac{1}{8DL(56)^{2L}}\qquad\text{and}\qquad h\le\frac{1}{8\beta L}\log\Bigl(\frac{1}{4DL\beta}\Bigr),
--   $$
--   then the Gibbs state $e^{-\beta H}/\mathrm{tr}(e^{-\beta H})$ is a convex combination of product states $\rho_1\otimes\cdots\otimes\rho_n$.
--
--   For fixed $L$ and $D$ the allowed field is of order $\log(1/\beta)/\beta$, which matches known entangled examples up to constants (formal version of Theorem 1.6).
--
--   **Formalization Note** $\log$ is the natural logarithm; $h$ is the supremum of $\|V_i\|$ over the sites (zero when $n=0$).
--
--   Differences from the source:
--   - encoding: n-qubit operators; H = V + W with terms h_a of distinct supports Z_a → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ; HamData (Fin n) n with w Z the term of support Z and IsQubitLocal; reason: the same operators and Hamiltonians (the paper combines terms with equal support)
--   - encoding: 0 < β ≤ 1/(8DL(56)^{2L}) → 0 < β and 8DL·56^{2L}·β ≤ 1; reason: the same interval, without division
--   - encoding: a convex combination of product states → membership in convexHull ℝ of the set of products ρ_1 ⊗ ⋯ ⊗ ρ_n of single-qubit density matrices; reason: finite convex combinations; the set of product states is compact, so its convex hull is closed and contains every infinite mixture
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Theorem 9.1, p.41; informal Theorem 1.6, p.5

import Mathlib
import Definitions.Def_FermiHubbardMix_Supplement_IsQubitLocal
import Definitions.Def_FermiHubbardMix_Supplement_productStates
import Definitions.Def_FermiHubbardMix_gibbs
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix.Supplement

/-- **Theorem 9.1 (Separability)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.41; informal Theorem 1.6, p.5). Let `H = V + W` on
`n` qubits, where `W` is a bounded `L`-local degree-`D` Hamiltonian and `V = ∑_i V_i` is an external
field with `V_i` supported on site `i` only, and let `h = max_i ‖V_i‖`. If
`0 < β ≤ 1/(8DL·56^{2L})` and `h ≤ (1/(8βL)) log(1/(4DLβ))`, then the Gibbs state
`e^{-βH}/tr(e^{-βH})` is a convex combination of product states.

**Formalization Note** `β ≤ 1/(8DL·56^{2L})` is written `8DL·56^{2L}·β ≤ 1`; `h` is the supremum over the
sites of the operator norms of the onsite terms (`0` when `n = 0`); `log` is natural. A convex
combination of product states is membership in `convexHull ℝ (productStates n)`, product states having
arbitrary (mixed) single-qubit factors. -/
theorem theorem_9_1 {n : ℕ} (H : HamData (Fin n) n) (hH : IsQubitLocal H) (L D : ℕ)
    (hLD : H.BoundedCouplings L D) (β : ℝ) (hβ : 0 < β)
    (hβLD : 8 * (D : ℝ) * L * 56 ^ (2 * L) * β ≤ 1)
    (hh : (⨆ i : Fin n, opNorm (H.v i)) ≤ Real.log (1 / (4 * (D : ℝ) * L * β)) / (8 * β * L)) :
    gibbs β H.ham ∈ convexHull ℝ (productStates n) := by sorry

end FermiHubbardMix.Supplement
