-- Prove2me | Theorems.Thm_DynHaussler_lemma_34
-- name    : DynHaussler.lemma_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:37:01.893224+00:00
-- url     : https://prove2.me/theorems/ae6464a1-da7e-481b-ae6c-9f4a9f024032
-- title:
--   Lemma 34 — $\mathrm{Ldim}(H_d)=\mathrm{sfat}_\gamma(H_d)=d$ for the fixed class
-- statement:
--   For every integer $d\ge1$ and $0<\gamma\le1$, the fixed class $H_d$ of zero-extended finite-field hyperplane indicators on $X_d=\bigsqcup_{m\ge1}(\{m\}\times\mathbb F_{2^m}^d)$ (Eqs. (108)–(109)) satisfies
--   $$
--   \mathrm{Ldim}(H_d)=\mathrm{sfat}_\gamma(H_d)=d. \tag{110}
--   $$
--
--   The lemma supplies the dimension identities of Theorem 6.
--
--   **Formalization Note** $\mathbb F_{2^m}$ is `GaloisField 2 m`; both dimensions lie in `ℕ∞`.
--
--   Differences from the source:
--   - encoding: a field F_{2^m} with 2^m elements → GaloisField 2 m; reason: any two fields with 2^m elements are isomorphic, and the class is defined the same way on each
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 34, Eq. (110), p.46 (PDF p.48); class (106)–(109), p.46

import Mathlib
import Definitions.Def_DynHaussler_Hd
import Definitions.Def_DynHaussler_ldim
import Definitions.Def_NondualOpt_sfat

set_option autoImplicit false

namespace DynHaussler

/-- **Lemma 34 (Dimension of the fixed class).** For every integer `d ≥ 1` and `0 < γ ≤ 1`,
`Ldim(H_d) = sfat_γ(H_d) = d` (Eq. (110)), where `H_d` is the class (109) of zero-extended
finite-field hyperplane indicators on `X_d = ⨆_{m ≥ 1} ({m} × F_{2^m}^d)` (108).
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 34, Eq. (110), p.46 (PDF p.48); the class (106)–(109), p.46.

**Formalization Note** `F_{2^m}` is `GaloisField 2 m`; both dimensions lie in `ℕ∞`. -/
theorem lemma_34 (d : ℕ) (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ldim (Hd d) = d ∧ NondualOpt.sfat (Hd d) γ = d := by sorry

end DynHaussler
