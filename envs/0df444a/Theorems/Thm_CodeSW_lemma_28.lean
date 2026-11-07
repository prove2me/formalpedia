-- Prove2me | Theorems.Thm_CodeSW_lemma_28
-- name    : CodeSW.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:28:20.758192+00:00
-- url     : https://prove2.me/theorems/954fd5d5-e1ac-46d6-a90b-f174f5d10c32
-- title:
--   Lemma 28 — self-adjointness, idempotence, commutation and norms of $M^*M$ and $T_e$ on $L_2(\mu)$
-- statement:
--   Let $0<p<1$, let $\mu$ be the generalized FK measure, and let $M,M^*,T_e$ be the operators of Appendix A. Then:
--
--   1. $M^*M$ and $T_e$ are self-adjoint in $L_2(\mu)$ for every $e\in E$;
--   2. $MM^*(A,B)=\mathbf 1(A=B)$, and thus $M^*MM^*M=M^*M$;
--   3. $T_eT_e=T_e$ and $T_eT_{e'}=T_{e'}T_e$ for all $e,e'\in E$;
--   4. $\|T_e\|_\mu=1$ and $\|M^*M\|_\mu=1$.
--
--   These identities let the Swendsen-Wang chain and the single-check chain be written in terms of one family of commuting projections.
--
--   Differences from the source:
--   - encoding: ‖f‖_π := ⟨f, f⟩_π (p.34) with ⟨f,g⟩_π = ∑ f(x)f(g)π(x) (p.33) → ‖f‖_µ = √⟨f, f⟩_µ and ⟨f,g⟩_µ = ∑ f g µ; reason: the printed f(g) is a typo, and the supremum defining each operator norm is 1 under either convention for the norm
--   - encoding: p from p = 1 − e^{−2β} → 0 < p < 1 as a hypothesis; reason: β ∈ (0, ∞) is exactly p ∈ (0, 1)
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Lemma 28, p.34

import Definitions.Def_CodeSW_fk
open Matrix

namespace CodeSW

/-- **Lemma 28.** Let `M`, `M*` and `T_e` be the FK operators, `µ` the FK measure (10), and
`0 < p < 1`. Then
1. `M*M` and `T_e` are self-adjoint in `L²(µ)`;
2. `MM*(A, B) = 1(A = B)` and thus `M*MM*M = M*M`;
3. `T_eT_e = T_e` and `T_eT_{e'} = T_{e'}T_e` for all `e, e' ∈ E`;
4. `‖T_e‖_µ = 1` and `‖M*M‖_µ = 1`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, Lemma 28, p.34). -/
theorem lemma_28 {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) :
    (IsSelfAdjointMu (fk h p) (liftMStar (c := c) (n := n) * liftM h) ∧
      ∀ e : Fin c, IsSelfAdjointMu (fk h p) (resample h p e)) ∧
    (liftM h * liftMStar (c := c) (n := n) = 1 ∧
      (liftMStar (c := c) (n := n) * liftM h) * (liftMStar (c := c) (n := n) * liftM h) =
        liftMStar (c := c) (n := n) * liftM h) ∧
    (∀ e : Fin c, resample h p e * resample h p e = resample h p e) ∧
    (∀ e e' : Fin c, resample h p e * resample h p e' = resample h p e' * resample h p e) ∧
    (∀ e : Fin c, opNormMu (fk h p) (resample h p e) = 1) ∧
    opNormMu (fk h p) (liftMStar (c := c) (n := n) * liftM h) = 1 := by sorry

end CodeSW
