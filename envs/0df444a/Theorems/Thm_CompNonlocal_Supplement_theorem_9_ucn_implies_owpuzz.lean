-- Prove2me | Theorems.Thm_CompNonlocal_Supplement_theorem_9_ucn_implies_owpuzz
-- name    : CompNonlocal.Supplement.theorem_9_ucn_implies_owpuzz
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:13:58.691859+00:00
-- url     : https://prove2.me/theorems/ccdaf581-b033-4078-aa5f-6bc46eedecea
-- title:
--   Theorem 9 — UCN implies one-way puzzles
-- statement:
--   Assume universal computational nonlocality (Assumption 2): every entangled state is computationally nonlocal in the sense of Definition 10, i.e. has a certificate with a polynomial number of independent rounds, uniform quantum polynomial-time verifier and honest players, soundness against all polynomial-size players with classical advice on all separable states of the same registers, and an inverse-polynomial gap. The verifier may retain a classical or quantum trapdoor.
--
--   Then ordinary one-way puzzles [KT24] exist against polynomial-size quantum adversaries with classical advice.
--
--   Differences from the source:
--   - generalization: UCN for all finite-dimensional Hilbert spaces H_A, H_B → UCN required only for qubit registers (C²)^{⊗n_A} ⊗ (C²)^{⊗n_B}, all n_A, n_B; reason: the hypothesis asks less: qubit registers are finite-dimensional spaces, so the paper's UCN implies this one and the Lean theorem implies the paper's
--   - encoding: OWPuzz with Samp(1^κ) → (puzz, ans) and Ver(puzz, ans) → puzz = first l(κ) bits of the sampler's classical output, ans = the rest; Ver : Str → Str → Bool independent of κ; reason: a fixed-position split is a special sampler and a κ-independent Ver is the [KT24] syntax, so the Lean conclusion implies the paper's
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Theorem 9, p.63 (proof §11, pp.63–68)

import Mathlib
import Definitions.Def_CompNonlocal_Supplement_UCN
import Definitions.Def_CompNonlocal_Supplement_IsOWPuzz

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Theorem 9, p.63: "Theorem 9 (UCN implies OWPuzz). If UCN holds with an inverse-polynomial
certification gap, then ordinary OWPuzz exist against polynomial-size quantum adversaries with
classical advice. The verifier may retain a classical or quantum trapdoor."

If `UCN` holds (Assumption 2 with Definition 10: every entangled state on qubit registers has a
certificate with a polynomial number `k(κ)` of independent rounds, completeness `c`, soundness `s`
against all polynomial-size players with advice on all separable states of the same registers, and
`c − s > 1/poly`; the verifier's `Q` may retain a quantum register `td`), then there is a one-way
puzzle (`IsOWPuzz`, [KT24]): a uniform QPT sampler and a verification function with correctness
`1 − negl` and security `negl` against polynomial-size adversaries with advice.

**Formalization Note** `UCN` quantifies over qubit registers of every size, which asks less than the
paper's "all finite-dimensional Hilbert spaces"; the puzzle's `puzz`/`ans` split is at a fixed
position `l κ` and `Ver` does not depend on `κ`, which asks more of the conclusion. -/
theorem theorem_9_ucn_implies_owpuzz (h : UCN) :
    ∃ (Samp : Family) (l : ℕ → ℕ) (Ver : Str → Str → Bool), IsOWPuzz Samp l Ver := by sorry

end CompNonlocal.Supplement
