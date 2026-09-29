-- Prove2me | Theorems.Thm_CuspidalType_character_unipotent
-- name    : CuspidalType.character_unipotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/2c69215e-fdfc-5ec0-9634-f18e8e122e6f
-- title:
--   Cuspidal character equals -1 at non-trivial unipotents
-- statement:
--   Let $q$ be a prime, let $K$ be an algebraically closed field of characteristic zero, and let $V$ be a non-zero finite-dimensional $K$-vector space. Let $\rho$ be a representation of $\mathrm{GL}_2(\mathbb{Z}/q) =$ `GL2 q`, the general linear group of $2\times 2$ matrices over $\mathbb{Z}/q$, on $V$. Assume two hypotheses: irreducibility, in the form that every subrepresentation of $\rho$ whose underlying submodule is not $\bot$ has underlying submodule $\top$; and cuspidality, in the form that the only vector $v \in V$ with $\rho(u(x))v = v$ for all $x \in \mathbb{Z}/q$ is $v = 0$, where $u(x) =$ `unipotent q x` denotes the unit of the matrix ring given by $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ with inverse $\begin{pmatrix}1&-x\\0&1\end{pmatrix}$. Then for every $t \in \mathbb{Z}/q$ with $t \neq 0$, the character of $\rho$, i.e. the trace of the endomorphism $\rho(u(t))$ of $V$, equals $-1$ in $K$.
--
--   This is the standard value of the character of an irreducible cuspidal representation of $\mathrm{GL}_2(\mathbb{F}_q)$ at a non-trivial upper unipotent element, reflecting that the restriction to the upper unipotent subgroup is the sum of all $q-1$ non-trivial additive characters of $\mathbb{F}_q$, each once. It feeds into the identification of such representations with a model of prescribed type, used in [`CuspidalType.exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central`](thm.html#CuspidalType.exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central) and [`CuspidalType.IsCuspidalOfType.exists_linearEquiv_comm_of_isCuspidalOfType`](thm.html#CuspidalType.IsCuspidalOfType.exists_linearEquiv_comm_of_isCuspidalOfType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_character_unipotent.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.character_unipotent
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hirr : ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) {t : ZMod q} (ht : t ≠ 0) :
    ρ.character (unipotent q t) = -1 := by sorry
