-- Prove2me | Theorems.Thm_DDNNFNeg_theorem_3_1
-- name    : DDNNFNeg.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:08.013106+00:00
-- url     : https://prove2.me/theorems/e7e7ed2b-7795-4325-b359-b723e46df465
-- title:
--   Theorem 3.1 [BCMS16] — every DNNF computing $f$ has at least $\mathrm{Cov}^m_1(f)$ gates
-- statement:
--   For every Boolean function $f : \{0,1\}^X \to \{0,1\}$ with $|X| \ge 2$, every DNNF computing $f$ has at least $\mathrm{Cov}^m_1(f)$ gates:
--   $$
--   \mathrm{Cov}^m_1(f) \le |D| \quad \text{for every DNNF } D \text{ computing } f .
--   $$
--
--   Applied to $\neg f_G$, whose $1$-cover number is $\mathrm{Cov}^m_0(f_G)$, this turns the rectangle-cover lower bound into the DNNF lower bound of Theorem 5.3.
--
--   Differences from the source:
--   - generalization: every DNNF (literal input gates only) → every DNNF, constant leaves allowed; reason: a larger class of circuits; every constant-free DNNF is one, so the statement specializes to the paper's
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Theorem 3.1, p.9

import Mathlib
import Definitions.Def_DDNNFNeg_NNF_Computes
import Definitions.Def_DDNNFNeg_NNF_IsDNNF
import Definitions.Def_DDNNFNeg_coverNumberMulti

namespace DDNNFNeg

/-- **Theorem 3.1** [BCMS16] (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.9): for every Boolean function `f : {0,1}^X → {0,1}` with
`|X| ≥ 2`, every DNNF computing `f` has at least `Cov^m_1(f)` gates.

**Formalization Note** The DNNF may also use constant leaves (`IsDNNF` without `IsConstFree`), a
larger class than the paper's; every constant-free DNNF is one, so this specializes to the
paper's statement. -/
theorem theorem_3_1 {X : Type*} [Fintype X] [DecidableEq X] (hX : 2 ≤ Fintype.card X)
    (f : (X → Bool) → Bool) (D : NNF X) (hD : D.IsDNNF) (hf : D.Computes f) :
    coverNumberMulti true f ≤ D.size := by sorry

end DDNNFNeg
