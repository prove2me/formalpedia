-- Prove2me | Theorems.Thm_Arxiv1606_00062_krylov_binomial_identity
-- name    : Arxiv1606_00062.krylov_binomial_identity
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T22:19:41.394695+00:00
-- url     : https://prove2.me/theorems/7bca1ebb-379c-4844-8771-a799fd5d13e9
-- title:
--   Eq. (32): the Krylov subspace is spanned by the multiple scattering iterations
-- statement:
--   Let $V$ be a complex Hilbert space, $\mathcal T:V\to V$ a bounded linear operator, $g\in V$, and $\eta^\ell=\mathcal T^\ell g$ the multiple scattering iterations. Then for every $n\ge0$,
--
--   $$(\mathcal I-\mathcal T)^n g=\sum_{\ell=0}^{n}\binom{n}{\ell}(-1)^\ell\,\mathcal T^\ell g=\sum_{\ell=0}^{n}\binom{n}{\ell}(-1)^\ell\,\eta^\ell,$$
--
--   and consequently, for every $m\ge0$, the Krylov subspace satisfies
--
--   $$K_m=\operatorname{span}\{g,(\mathcal I-\mathcal T)g,\dots,(\mathcal I-\mathcal T)^{m-1}g\}=\operatorname{span}\{\eta^0,\dots,\eta^{m-1}\}.$$
--
--   **Formalization Note** $\mathcal T$ is an arbitrary bounded operator on a complex Hilbert space; the paper's iteration operator (7) on $L^2(\partial\Omega)$ is one instance, and the identity uses only linearity. The paper's further remark that information about $K_m$ can be obtained in frequency-independent time is a statement about computational cost and is not formalized. The case $m=0$ (both spans are $\{0\}$) is included.
-- source:
--   Boubendir, Ecevit and Reitich, Acceleration of an iterative method for the evaluation of high-frequency multiple scattering effects, arXiv:1606.00062v1 (2016), claim c005; Section 5, eq. (32) and the display following it, PDF pp. 11-12

import Mathlib
import Definitions.Def_Arxiv1606_00062_Basic

open Filter Topology

namespace Arxiv1606_00062

theorem krylov_binomial_identity {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (T : V →L[ℂ] V) (g : V) :
    (∀ n : ℕ, ((1 - T) ^ n) g =
      ∑ l ∈ Finset.range (n + 1), ((n.choose l : ℂ) * (-1) ^ l) • msIter T g l) ∧
    (∀ m : ℕ, krylovSpace T g m = Submodule.span ℂ (msIter T g '' {l | l < m})) := by sorry

end Arxiv1606_00062
