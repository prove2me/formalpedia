-- Prove2me | Theorems.Thm_DantzigSelector_Sparse_cone_constraint
-- name    : DantzigSelector.Sparse.cone_constraint
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:39:56.56232+00:00
-- url     : https://prove2.me/theorems/fa7e369b-d6e6-4f89-ac84-8f34cbe616a5
-- title:
--   Eq. (3.2) — the cone constraint $\|h_{T_0^c}\|_{\ell_1}\le\|h_{T_0}\|_{\ell_1}$
-- statement:
--   Let $\beta,h\in\mathbb R^p$ and let $T_0\subseteq\{1,\dots,p\}$ be a set outside of which $\beta$ vanishes. If
--   $$
--   \|\beta+h\|_{\ell_1}\le\|\beta\|_{\ell_1},
--   $$
--   then $h$ obeys the **cone constraint**
--   $$
--   \|h_{T_0^c}\|_{\ell_1}\le\|h_{T_0}\|_{\ell_1},
--   $$
--   where $h_{T}$ denotes the vector equal to $h$ on $T$ and zero outside.
--
--   In the proof of Theorem 1.1, $\beta$ is the true parameter, $\hat\beta=\beta+h$ is a Dantzig selector, and the hypothesis holds because $\beta$ is feasible for (DS) while $\hat\beta$ minimizes the $\ell_1$ norm. The cone constraint is one of the two geometric constraints on the error $h$.
--
--   **Formalization Note** The paper takes $T_0$ to be the support $\{i:\beta_i\ne0\}$; the statement here allows any $T_0$ containing the support, which is how it is used when $T_0$ is enlarged to cardinality exactly $S$ for Lemma 3.1.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 15, Section 3.1, Eq. (3.2)

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
open CandesTao.Decoding

namespace DantzigSelector.Sparse

/-- Eq. (3.2): if `β` vanishes outside `T0` and `‖β + h‖_{ℓ1} ≤ ‖β‖_{ℓ1}`, then `h` obeys the
cone constraint `‖h_{T0ᶜ}‖_{ℓ1} ≤ ‖h_{T0}‖_{ℓ1}`. -/
theorem cone_constraint {p : ℕ} (β h : Fin p → ℝ) (T0 : Finset (Fin p))
    (hβ : SupportedOn β T0) (hle : l1Norm (β + h) ≤ l1Norm β) :
    l1On h T0ᶜ ≤ l1On h T0 := by sorry

end DantzigSelector.Sparse
