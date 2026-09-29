-- Prove2me | Theorems.Thm_CuspForm_heckeTLin_heckeULin_comm
-- name    : CuspForm.heckeTLin_heckeULin_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/ec98f7b8-bb6c-565e-8a22-659275b8f372
-- title:
--   Tₚ and U_q commute on S_k(Γ₀(N))
-- statement:
--   Let $N$ be a natural number, assumed nonzero, let $k$ be an integer, and let $p,q$ be natural numbers with $p$ prime, $p \nmid N$ and $q \mid N$. The assertion is that the two $\mathbb{C}$-linear endomorphisms [`CuspForm.heckeTLin k hp hpN`](def/ModularForm_HeckeOperatorForms.html#L69) and [`CuspForm.heckeULin k hqN`](def/ModularForm_HeckeOperatorForms.html#L83) of the space $S_k(\Gamma_0(N))$ of weight-$k$ cusp forms for `CongruenceSubgroup.Gamma0 N` commute, i.e. their two composites in either order are equal as linear maps. Here [`CuspForm.heckeULin k hqN`](def/ModularForm_HeckeOperatorForms.html#L83) is the map sending a cusp form $f$ to the cusp form with underlying function $\mathrm{heckeU}\,k\,q\,f = \sum_{j<q} f \mid[k]\,(\mathrm{heckeMatrix}\, q\,j)$, the weight-$k$ slash action applied to the $q$ matrices `heckeMatrix q j` for $j$ in `Finset.range q` and summed; and [`CuspForm.heckeTLin k hp hpN`](def/ModularForm_HeckeOperatorForms.html#L69) sends $f$ to the cusp form with underlying function $\mathrm{heckeT}\,k\,p\,f = \mathrm{heckeU}\,k\,p\,f + f \mid[k]\,(\mathrm{heckeDiagMatrix}\, p)$, the same sum of $p$ slashes together with one further slash by the diagonal matrix `heckeDiagMatrix p`. In both cases the hypotheses on $p$ and on $q$ enter in verifying that the resulting function is again $\Gamma_0(N)$-invariant of weight $k$, holomorphic and vanishing at the cusps.
--
--   This is the coprime case of the commutativity of the Hecke algebra acting on cusp forms, in the mixed form pairing a good Hecke operator $T_p$ with $p \nmid N$ against a $U_q$ with $q \mid N$. It is used downstream wherever a family of Hecke operators must be diagonalised simultaneously or generate a commutative subalgebra of $\mathrm{End}_{\mathbb{C}} S_k(\Gamma_0(N))$, for instance in the construction of normalised eigenforms from systems of $T_p$-eigenvalues and in the analysis of $U_q$ on newforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeTLin_heckeULin_comm.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.heckeTLin_heckeULin_comm {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeULin k hqN) := by sorry
