-- Prove2me | Theorems.Thm_DotySW_Deranged_deranged_schurWeyl
-- name    : DotySW.Deranged.deranged_schurWeyl
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:03.255485+00:00
-- url     : https://prove2.me/theorems/831e6c5d-190d-4d8b-b183-8e57ee52e8d5
-- title:
--   §4.3, Eqs. (19)–(20) — $\mathrm{GL}_n$ and $e\mathcal B^{(n)}_{r,r}e$ are mutual centralizers on $\mathfrak{sl}_n^{\otimes r}$
-- statement:
--   Let $n\ge2r$. Let $\mathrm{GL}_n(\mathbb C)$ act on $\mathfrak{sl}_n^{\otimes r}$ by conjugation in each slot, and let $e=\prod_i(1-n^{-1}c_{i,-i})$ in the walled Brauer algebra $\mathcal B^{(n)}_{r,r}$. Then:
--
--   1. every element of the deranged algebra $e\mathcal B^{(n)}_{r,r}e$ maps $\mathfrak{sl}_n^{\otimes r}$ into itself under $\sigma$;
--   2. the operators so obtained are all of the commutant of $\mathrm{GL}_n$:
--   $$
--   \sigma(e\mathcal B^{(n)}_{r,r}e)=\mathrm{End}_{\mathrm{GL}_n}(\mathfrak{sl}_n^{\otimes r});\tag{20}
--   $$
--   3. the span of $\mathrm{GL}_n$ is all of the commutant of those operators:
--   $$
--   \rho(\mathbb C\mathrm{GL}_n)=\mathrm{End}_{e\mathcal B^{(n)}_{r,r}e}(\mathfrak{sl}_n^{\otimes r}).\tag{19}
--   $$
--
--   This is Schur-Weyl duality with the natural module $V$ replaced by the adjoint module $\mathfrak{sl}_n$.
--
--   Differences from the source:
--   - encoding: $\mathcal B^{(x)}_{r,s}$ over $R[x]$ at $x=n$, over $\mathbb C$ → the published `WalledBrauerAlgebra ℂ r s n`; reason: §3.4 works over ℂ with x = n, and the published algebra has the diagrams as basis and loop parameter n
--   - encoding: $V^{r,s}=V^{\otimes r}\otimes V^{*\otimes s}$ with $\sigma$ restricted from $\mathcal B^{(n)}_{r+s}$ through $V\simeq V^*$ on $\mathrm O_n$ → vectors are functions on `Idx n (r + s)` and ρ, σ are matrices in the basis of the $e_i$ and the dual $e_i^*$, row = output, top row of a diagram = output; reason: a choice of coordinates, and $e_i\leftrightarrow e_i^*$ is the identification of p. 9
--   - encoding: $\rho(\mathbb C\mathrm{GL}_n)$ → the linear span of the operators ρ(g); reason: the image of the group algebra is by definition this span
--   - encoding: $\mathrm{End}_{e\mathcal B^{(n)}_{r,r}e}(\mathfrak{sl}_n^{\otimes r})$ → the commutant of `sigmaCorner n r` in the endomorphisms of `slTensor n r`; reason: an endomorphism commutes with the action of the algebra exactly when it commutes with the operators induced by the algebra
--   - encoding: $V=\mathbb C^n$ with $n\ge1$ understood → no positivity hypothesis on n; reason: n = 0 is the degenerate case V = 0, where the statement is still true, and no instance with n ≥ 1 changes
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.3, Eqs. (19)–(20), p. 11

import Mathlib
import Definitions.Def_DotySW_Deranged_rhoSl
import Definitions.Def_DotySW_Deranged_sigmaCorner

namespace DotySW.Deranged

/-- **Schur-Weyl duality for `GL_n` and the deranged algebra on `sl_n^{⊗r}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.3, Eqs. (19)–(20), p. 11.

For `n ≥ 2r`:
1. every element of `e B^{(n)}_{r,r} e` acts on `sl_n^{⊗r}` by restriction of `σ`;
2. (20): the operators so obtained are exactly `End_{GL_n}(sl_n^{⊗r})`;
3. (19): the span of `GL_n` on `sl_n^{⊗r}` is exactly the commutant of those operators.

**Formalization Note** `ρ(ℂGL_n)` is the linear span of the operators `rhoSl n r g`, for the whole
group `GL_n(ℂ)`. `End_{eBe}(sl_n^{⊗r})` is the commutant of `sigmaCorner n r`; clause 1 makes the
restriction meaningful. Both (19) and (20) are equalities. -/
theorem deranged_schurWeyl (n r : ℕ) (h : 2 * r ≤ n) :
    (∀ x ∈ corner n r, ∃ T : Module.End ℂ (slTensor n r), ActsBy n r x T) ∧
    sigmaCorner n r =
      (Subalgebra.centralizer ℂ (Set.range (rhoSl n r)) : Set (Module.End ℂ (slTensor n r))) ∧
    Submodule.span ℂ (Set.range (rhoSl n r)) =
      Subalgebra.toSubmodule (Subalgebra.centralizer ℂ (sigmaCorner n r)) := by sorry

end DotySW.Deranged
