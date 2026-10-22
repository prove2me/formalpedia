-- Prove2me | Theorems.Thm_EastinKnill_Transversal_infinitesimal_logical
-- name    : EastinKnill.Transversal.infinitesimal_logical
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:40.855013+00:00
-- url     : https://prove2.me/theorems/61dcbd18-d46a-46fd-bb19-2d9d9d98adaa
-- title:
--   Proof of Theorem 1, p. 3 — if $e^{i\varepsilon D}$ is logical for all $\varepsilon$, then $(I-P)DP=0$
-- statement:
--   Let $P$ be an operator on a finite-dimensional system and $D$ a Hermitian operator. Suppose that for every real $\varepsilon$ the unitary $e^{i\varepsilon D}$ is logical, i.e. $(I-P)e^{i\varepsilon D}P = 0$. Then
--
--   $$(I-P)\,D\,P = 0.$$
--
--   This is the derivative step of the proof of Theorem 1: an element $D$ of the Lie algebra of the identity component $\mathcal C$ generates a one-parameter group of logical gates, and differentiating at $\varepsilon = 0$ shows that $D$ itself preserves the code space.
--
--   **Formalization Note** The hypothesis "$D \in \mathfrak c$" is replaced by what the step uses: $e^{i\varepsilon D}$ is logical for all real $\varepsilon$. The factor $i$ and the Hermiticity of $D$ follow the physics convention of footnote 1. The exponential is `NormedSpace.exp`.
-- source:
--   Eastin & Knill, Restrictions on Transversal Encoded Quantum Gate Sets, arXiv:0811.4262v2, p. 3, proof of Theorem 1, display "0 = lim (I − P)[(e^{iεD} − I)/(iε)]P = (I − P)DP"

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix

namespace EastinKnill.Transversal

theorem infinitesimal_logical {n : Type*} [Fintype n] [DecidableEq n] (P D : Matrix n n ℂ)
    (hD : D.IsHermitian)
    (h : ∀ ε : ℝ, IsLogical P (NormedSpace.exp (((ε : ℂ) * Complex.I) • D))) :
    (1 - P) * D * P = 0 := by sorry

end EastinKnill.Transversal
