-- Prove2me | Theorems.Thm_ChebotarevDensity_zetaPrimeSum_asymp
-- name    : ChebotarevDensity.zetaPrimeSum_asymp
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-01T14:26:20.670682+00:00
-- url     : https://prove2.me/theorems/940ded15-01c1-473a-aa07-f9dc95fcf4c7
-- title:
--   Prime ideal zeta sum of a number field is log(1/(s-1)) + O(1)
-- statement:
--   Let $L$ be a number field with ring of integers $\mathcal O_L$, and write $\mathrm N\mathfrak p=\#(\mathcal O_L/\mathfrak p)$ for the absolute norm of a nonzero prime ideal $\mathfrak p$. Then there is a constant $C$ such that, for all real $s>1$ sufficiently close to $1$,
--   $$\Bigl|\ \sum_{\mathfrak p}\mathrm N\mathfrak p^{-s}-\log\frac1{s-1}\ \Bigr|\le C ,$$
--   where the sum runs over all nonzero prime ideals $\mathfrak p$ of $\mathcal O_L$.
--
--   In other words $\sum_{\mathfrak p}\mathrm N\mathfrak p^{-s}=\log\frac{1}{s-1}+O(1)$ as $s\downarrow1$. For $L=\mathbb Q$ this is the classical asymptotic $\sum_p p^{-s}\sim\log\frac1{s-1}$; for general $L$ it expresses that the Dedekind zeta function $\zeta_L$ has a simple pole at $s=1$. It is the analytic input behind the notion of Dirichlet density of sets of prime ideals and behind Frobenius's density theorem.
--
--   **Formalization Note** The sum is a `tsum` over `IsDedekindDomain.HeightOneSpectrum (𝓞 L)`, and the statement is made eventually in the filter `𝓝[>] 1`.
-- source:
--   Serre, A Course in Arithmetic, Ch. VI; Lang, Algebraic Number Theory, Ch. VIII §4 (Dedekind zeta functions and densities); Neukirch, Algebraic Number Theory, Ch. VII §13 (density of prime ideals; Frobenius density theorem)

import Definitions.Def_ChebotarevDensity_Aux

open Polynomial NumberField

namespace ChebotarevDensity

theorem zetaPrimeSum_asymp (L : Type) [Field L] [NumberField L] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
      |(∑' P : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
          (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) - Real.log (1 / (s - 1))| ≤ C := by sorry

end ChebotarevDensity
